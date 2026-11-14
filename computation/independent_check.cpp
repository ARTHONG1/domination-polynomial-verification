// Independent verifier for "Unimodality of domination polynomials of forests
// at upper-domination gaps three and four".
//
// Written from scratch on 2026-11-11 without reference to the earlier
// certificate code.  It differs from that code in every component:
//   * generation:  Beyer--Hedetniemi level sequences of ALL rooted trees,
//                  filtered to centroid-rooted representatives of free trees;
//   * completeness: rooted counts vs. A000081 recurrence, free counts vs.
//                  the Otter dissymmetry formula (both recomputed here);
//   * polynomial:  sequential child-merge three-state recurrence;
//   * ground truth: exhaustive subset enumeration for all trees of order <= BF.
//
// Usage: independent_check N_LO N_HI [BF [MOD RES]]   (prints one JSON object per order)
//   BF       largest order checked against exhaustive subset enumeration (default 15)
//   MOD RES  process only the rooted trees whose running index is RES modulo MOD
//            (for parallel runs; every process still traverses and counts all rooted
//            trees, and the free-tree counts of the MOD residue classes must add up)
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <utility>
#include <vector>
typedef unsigned long long u64;
typedef __uint128_t u128;
static const int MAXN = 31;

// order-independent fingerprint of the multiset of coefficient vectors
static u64 fingerprint(const u64 *d, int n) {
  u64 h = 1469598103934665603ULL;
  for (int j = 0; j <= n; ++j) { h ^= d[j]; h *= 1099511628211ULL; }
  h ^= h >> 30; h *= 0xbf58476d1ce4e5b9ULL; h ^= h >> 27; h *= 0x94d049bb133111ebULL; h ^= h >> 31;
  return h;
}

static int n;
static int L[MAXN], par[MAXN], sz[MAXN];
static std::vector<int> adj[MAXN];

struct Code { u64 bits; int len; };
static bool codeLess(const Code &a, const Code &b) {
  if (a.len != b.len) return a.len < b.len;
  return a.bits < b.bits;
}
static Code encode(int v, int p) {
  Code ch[MAXN]; int k = 0;
  for (int w : adj[v]) if (w != p) ch[k++] = encode(w, v);
  std::sort(ch, ch + k, codeLess);
  Code r; r.bits = 1; r.len = 1;
  for (int i = k - 1; i >= 0; --i) { r.bits = (r.bits << ch[i].len) | ch[i].bits; r.len += ch[i].len; }
  r.bits <<= 1; r.len += 1;
  return r;
}

// exact counts: rooted trees (A000081) and free trees (A000055)
static u64 R[MAXN + 1], T[MAXN + 1];
static void treeCounts() {
  R[0] = 0; R[1] = 1;
  for (int m = 2; m <= MAXN; ++m) {
    u128 s = 0;
    for (int j = 1; j <= m - 1; ++j) {
      u128 sd = 0;
      for (int d = 1; d <= j; ++d) if (j % d == 0) sd += (u128)d * R[d];
      s += sd * R[m - j];
    }
    if (s % (u128)(m - 1) != 0) { fprintf(stderr, "non-exact division\n"); exit(2); }
    R[m] = (u64)(s / (u128)(m - 1));
  }
  for (int m = 1; m <= MAXN; ++m) {
    u128 conv = 0;
    for (int k = 0; k <= m; ++k) conv += (u128)R[k] * R[m - k];
    u128 e = (m % 2 == 0) ? R[m / 2] : 0;
    if ((conv - e) % 2 != 0) { fprintf(stderr, "non-exact halving\n"); exit(2); }
    T[m] = (u64)((u128)R[m] - (conv - e) / 2);
  }
}

// domination polynomial by sequential child merging
static u64 A[MAXN][MAXN + 1], B[MAXN][MAXN + 1], C[MAXN][MAXN + 1];
static int deg_[MAXN];
static void dominationPolynomial(u64 *d) {
  for (int v = 0; v < n; ++v) {
    for (int j = 0; j <= n; ++j) A[v][j] = B[v][j] = C[v][j] = 0;
    A[v][1] = 1; C[v][0] = 1; deg_[v] = 1;
  }
  u64 na[MAXN + 1], nb[MAXN + 1], nc[MAXN + 1];
  for (int w = n - 1; w >= 1; --w) {            // children are numbered after parents
    int v = par[w];
    int dv = deg_[v], dw = deg_[w];
    for (int j = 0; j <= dv + dw; ++j) na[j] = nb[j] = nc[j] = 0;
    for (int i = 0; i <= dv; ++i) for (int j = 0; j <= dw; ++j) {
      u64 aw = A[w][j], bw = B[w][j], cw = C[w][j];
      na[i + j] += A[v][i] * (aw + bw + cw);
      nb[i + j] += B[v][i] * (aw + bw) + C[v][i] * aw;
      nc[i + j] += C[v][i] * bw;
    }
    deg_[v] = dv + dw;
    for (int j = 0; j <= deg_[v]; ++j) { A[v][j] = na[j]; B[v][j] = nb[j]; C[v][j] = nc[j]; }
  }
  for (int j = 0; j <= n; ++j) d[j] = A[0][j] + B[0][j];
}

static int independenceNumber() {
  int in1[MAXN], in0[MAXN];
  for (int v = 0; v < n; ++v) { in1[v] = 1; in0[v] = 0; }
  for (int w = n - 1; w >= 1; --w) {
    int v = par[w];
    in1[v] += in0[w];
    in0[v] += std::max(in0[w], in1[w]);
  }
  return std::max(in0[0], in1[0]);
}

// exhaustive ground truth (small orders): coefficients, gamma, Gamma, and the
// two-sided critical-vertex inequalities 2*gamma-|S| <= a(S) <= 2*Gamma-|S|.
static std::vector<uint32_t> domMask;
static bool bruteForce(const u64 *d, int gammaDP, int GammaDP, u64 &critViol) {
  uint32_t full = (n == 32) ? 0xffffffffu : ((1u << n) - 1), nb[MAXN];
  for (int v = 0; v < n; ++v) { nb[v] = 1u << v; for (int w : adj[v]) nb[v] |= 1u << w; }
  domMask.assign((size_t)1 << n, 0);
  u64 cnt[MAXN + 1] = {0};
  for (uint32_t S = 1; S <= full; ++S) {
    int low = __builtin_ctz(S);
    domMask[S] = domMask[S & (S - 1)] | nb[low];
    if (domMask[S] == full) cnt[__builtin_popcount(S)]++;
  }
  int gam = -1, Gam = -1;
  for (int j = 0; j <= n; ++j) if (cnt[j]) { gam = j; break; }
  // critical vertices
  std::vector<std::pair<int,int>> rec;   // (|S|, a(S))
  for (uint32_t S = 1; S <= full; ++S) if (domMask[S] == full) {
    int a = 0; uint32_t x = S;
    while (x) {
      int v = __builtin_ctz(x); x &= x - 1;
      // domination of S \ {v}: recompute by OR over remaining bits
      uint32_t Sm = S & ~(1u << v);
      if (domMask[Sm] != full) ++a;
    }
    int s = __builtin_popcount(S);
    if (a == s && s > Gam) Gam = s;
    rec.push_back(std::make_pair(s, a));
  }
  for (size_t i = 0; i < rec.size(); ++i) {
    int s = rec[i].first, a = rec[i].second;
    if (a < 2 * gam - s || a > 2 * Gam - s) ++critViol;
  }
  bool ok = (gam == gammaDP) && (Gam == GammaDP);
  for (int j = 0; j <= n; ++j) if (cnt[j] != d[j]) ok = false;
  return ok;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s N_LO N_HI [BF]\n", argv[0]); return 1; }
  int lo = atoi(argv[1]), hi = atoi(argv[2]);
  int BF = argc > 3 ? atoi(argv[3]) : 15;
  u64 MOD = argc > 5 ? strtoull(argv[4], 0, 10) : 1, RES = argc > 5 ? strtoull(argv[5], 0, 10) : 0;
  if (MOD < 1 || RES >= MOD) { fprintf(stderr, "need 0 <= RES < MOD\n"); return 1; }
  if (lo < 2 || hi > 30) { fprintf(stderr, "order range must lie in 2..30\n"); return 1; }
  treeCounts();
  for (n = lo; n <= hi; ++n) {
    u64 rooted = 0, freeTrees = 0, lcFail = 0, uniFail = 0, bfTrees = 0, bfMismatch = 0, critViol = 0;
    u64 coeffCount = 0, coeffSum = 0, supportFail = 0, maxCoeff = 0, mjFail = 0;
    double maxJump = -1e9;
    u64 fpSum = 0;
    std::map<std::pair<int,int>, u64> hist;        // (n-gamma, Gamma-gamma) -> count
    for (int i = 0; i < n; ++i) L[i] = i;
    for (;;) {
      ++rooted;
      if ((rooted - 1) % MOD == RES) {
      // parents and subtree sizes
      int last[MAXN];
      last[0] = 0; par[0] = -1;
      for (int i = 1; i < n; ++i) { par[i] = last[L[i] - 1]; last[L[i]] = i; }
      for (int i = 0; i < n; ++i) sz[i] = 1;
      for (int i = n - 1; i >= 1; --i) sz[par[i]] += sz[i];
      bool centroid = true; int other = -1;
      for (int i = 1; i < n; ++i) if (par[i] == 0) {
        if (2 * sz[i] > n) { centroid = false; break; }
        if (2 * sz[i] == n) other = i;
      }
      if (centroid) {
        for (int v = 0; v < n; ++v) adj[v].clear();
        for (int i = 1; i < n; ++i) { adj[i].push_back(par[i]); adj[par[i]].push_back(i); }
        bool accept = true;
        if (other >= 0) {
          Code c0 = encode(0, -1), c1 = encode(other, -1);
          // the two centroid rootings are two rooted trees unless they coincide
          if (c1.bits < c0.bits) accept = false;
        }
        if (accept) {
          ++freeTrees;
          u64 d[MAXN + 1];
          dominationPolynomial(d);
          int gam = 0; while (gam <= n && d[gam] == 0) ++gam;
          int Gam = independenceNumber();
          for (int j = gam; j <= n; ++j) if (d[j] == 0) ++supportFail;
          if (d[n] != 1) ++supportFail;
          bool lc = true;
          for (int j = 1; j < n; ++j) if ((u128)d[j] * d[j] < (u128)d[j - 1] * d[j + 1]) lc = false;
          if (!lc) {
            ++lcFail;
            if (lcFail <= 20) {                  // witness: parent array and coefficients
              fprintf(stderr, "NONLOGCONCAVE n=%d parents:", n);
              for (int i = 1; i < n; ++i) fprintf(stderr, " %d", par[i]);
              fprintf(stderr, " coefficients:");
              for (int q = 0; q <= n; ++q) fprintf(stderr, " %llu", d[q]);
              fprintf(stderr, "\n");
            }
          }
          // mean-jump inequality c_{j+1} - c_j <= 2, in the integer form
          // (n-j+1) d_{j-1} d_{j+1} <= d_j d_{j+1} + (n-j) d_j^2   (gamma <= j < n)
          bool mj = true;
          for (int q = gam; q < n; ++q) {
            u128 lhs = (u128)(n - q + 1) * d[q - 1] * d[q + 1];
            u128 rhs = (u128)d[q] * d[q + 1] + (u128)(n - q) * d[q] * d[q];
            if (lhs > rhs) mj = false;
            double J = 1.0 + (double)(n - q + 1) * (double)d[q - 1] / (double)d[q]
                           - (double)(n - q) * (double)d[q] / (double)d[q + 1];
            if (J > maxJump) maxJump = J;
          }
          if (!mj) {
            ++mjFail;
            if (mjFail <= 20) {
              fprintf(stderr, "MEANJUMP>2 n=%d parents:", n);
              for (int i = 1; i < n; ++i) fprintf(stderr, " %d", par[i]);
              fprintf(stderr, " coefficients:");
              for (int q = 0; q <= n; ++q) fprintf(stderr, " %llu", d[q]);
              fprintf(stderr, "\n");
            }
          }
          int j = 0; while (j < n && d[j] <= d[j + 1]) ++j;
          while (j < n && d[j] >= d[j + 1]) ++j;
          if (j != n) ++uniFail;
          for (int q = 0; q <= n; ++q) { coeffSum += d[q]; if (d[q] > maxCoeff) maxCoeff = d[q]; }
          coeffCount += n + 1;
          fpSum += fingerprint(d, n);
          hist[std::make_pair(n - gam, Gam - gam)]++;
          if (n <= BF) { ++bfTrees; if (!bruteForce(d, gam, Gam, critViol)) ++bfMismatch; }
        }
      }
      }
      // Beyer--Hedetniemi successor
      int p = n - 1; while (p >= 1 && L[p] < 2) --p;
      if (p < 1) break;
      int q = p - 1; while (L[q] != L[p] - 1) --q;
      for (int i = p; i < n; ++i) L[i] = L[i - (p - q)];
    }
    printf("{\"n\":%d,\"mod\":%llu,\"res\":%llu,\"rooted_generated\":%llu,\"rooted_expected\":%llu,\"free_generated\":%llu,\"free_expected\":%llu,"
           "\"logconcavity_failures\":%llu,\"unimodality_failures\":%llu,\"support_failures\":%llu,"
           "\"bruteforce_trees\":%llu,\"bruteforce_mismatches\":%llu,\"critical_bound_violations\":%llu,"
           "\"coefficients\":%llu,\"total_dominating_sets\":%llu,\"max_coefficient\":%llu,"
           "\"mean_jump_violations\":%llu,\"max_mean_jump\":%.6f,\"fingerprint\":\"%016llx\",\"hist\":[",
           n, MOD, RES, rooted, R[n], freeTrees, T[n], lcFail, uniFail, supportFail, bfTrees, bfMismatch, critViol,
           coeffCount, coeffSum, maxCoeff, mjFail, maxJump, fpSum);
    bool first = true;
    for (auto &kv : hist) { printf("%s[%d,%d,%llu]", first ? "" : ",", kv.first.first, kv.first.second, kv.second); first = false; }
    printf("]}\n");
    fflush(stdout);
    if (rooted != R[n] || (MOD == 1 && freeTrees != T[n])) { fprintf(stderr, "COUNT MISMATCH at n=%d\n", n); return 3; }
  }
  return 0;
}

