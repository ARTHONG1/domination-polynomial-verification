// Second, independent exhaustive check of log-concavity of the domination
// polynomials of all trees of a given order.
//
// Components (all different from independent_check.cpp):
//   * generation:  free trees by the Wright--Richmond--Odlyzko--McKay (WROM)
//                  level-sequence algorithm [SIAM J. Comput. 15 (1986) 540-548].
//                  The two successor routines below are a C++ rendering of the
//                  Beyer--Hedetniemi/WROM iteration as implemented in NetworkX
//                  (generators/nonisomorphic_trees.py, BSD-3-Clause, (c) NetworkX
//                  developers; see third_party/NETWORKX-LICENSE.txt);
//   * completeness: number of generated trees vs. Otter's formula;
//   * polynomial:  product form  A = z*prod(A+B+C),  B = prod(A+B) - prod(B),
//                  C = prod(B)  over the children;
//   * Gamma:       n minus a maximum matching (greedy from the leaves).
// It prints the same summary fields as independent_check.cpp, including the
// order-independent fingerprint of the multiset of coefficient vectors.
//
// Usage: wrom_check N_LO N_HI
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
typedef std::vector<int> Layout;

static bool next_rooted(Layout &a, int p = -1) {
  int n = (int)a.size();
  if (p < 0) { p = n - 1; while (p > 0 && a[p] == 1) --p; }
  if (p == 0) return false;
  int q = p - 1;
  while (q >= 0 && a[q] != a[p] - 1) --q;
  if (q < 0) { fprintf(stderr, "rooted predecessor absent\n"); exit(2); }
  for (int i = p; i < n; ++i) a[i] = a[i - p + q];
  return true;
}
static int split_position(const Layout &a) {
  bool first = false;
  for (int i = 0; i < (int)a.size(); ++i) if (a[i] == 1) { if (first) return i; first = true; }
  return (int)a.size();
}
static bool next_free(Layout &a) {
  int n = (int)a.size();
  int m = split_position(a);
  int lh = 0, rh = 0;
  for (int i = 1; i < m; ++i) lh = std::max(lh, a[i] - 1);
  for (int i = m; i < n; ++i) rh = std::max(rh, a[i]);
  int ll = m - 1, rl = n - m + 1;
  bool valid = (rh >= lh);
  if (valid && rh == lh) {
    if (ll > rl) valid = false;
    else if (ll == rl) {
      for (int i = 0; i < ll; ++i) {
        int l = a[1 + i] - 1, r = i == 0 ? 0 : a[m + i - 1];
        if (l > r) { valid = false; break; }
        if (l < r) break;
      }
    }
  }
  if (valid) return true;
  int p = ll;
  bool adjust = a[p] > 2;
  if (!next_rooted(a, p)) return false;
  if (adjust) {
    m = split_position(a);
    lh = 0;
    for (int i = 1; i < m; ++i) lh = std::max(lh, a[i] - 1);
    int suffix = lh + 1;
    for (int i = 0; i < suffix; ++i) a[n - suffix + i] = i + 1;
  }
  return true;
}

static u64 fingerprint(const u64 *d, int n) {
  u64 h = 1469598103934665603ULL;
  for (int j = 0; j <= n; ++j) { h ^= d[j]; h *= 1099511628211ULL; }
  h ^= h >> 30; h *= 0xbf58476d1ce4e5b9ULL; h ^= h >> 27; h *= 0x94d049bb133111ebULL; h ^= h >> 31;
  return h;
}

struct Poly { u64 c[MAXN + 1]; int deg; };
static void mulInto(Poly &acc, const Poly &f) {
  u64 t[MAXN + 1];
  int nd = acc.deg + f.deg;
  for (int i = 0; i <= nd; ++i) t[i] = 0;
  for (int i = 0; i <= acc.deg; ++i) if (acc.c[i]) for (int j = 0; j <= f.deg; ++j) t[i + j] += acc.c[i] * f.c[j];
  acc.deg = nd;
  for (int i = 0; i <= nd; ++i) acc.c[i] = t[i];
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s N_LO N_HI\n", argv[0]); return 1; }
  int lo = atoi(argv[1]), hi = atoi(argv[2]);
  if (lo < 2 || hi > 30) { fprintf(stderr, "order range must lie in 2..30\n"); return 1; }
  // Otter's count of free trees
  u64 R[MAXN + 1], T[MAXN + 1];
  R[0] = 0; R[1] = 1;
  for (int m = 2; m <= MAXN; ++m) {
    u128 s = 0;
    for (int j = 1; j < m; ++j) { u128 sd = 0; for (int e = 1; e <= j; ++e) if (j % e == 0) sd += (u128)e * R[e]; s += sd * R[m - j]; }
    R[m] = (u64)(s / (u128)(m - 1));
  }
  for (int m = 1; m <= MAXN; ++m) {
    u128 conv = 0;
    for (int k = 1; k < m; ++k) conv += (u128)R[k] * R[m - k];
    u128 e = (m % 2 == 0) ? R[m / 2] : 0;
    T[m] = (u64)((u128)R[m] - (conv - e) / 2);
  }
  static Poly P1[MAXN], P2[MAXN], P3[MAXN];
  for (int n = lo; n <= hi; ++n) {
    Layout a;
    for (int d = 0; d <= n / 2; ++d) a.push_back(d);
    for (int d = 1; d < (n + 1) / 2; ++d) a.push_back(d);
    u64 count = 0, lcFail = 0, uniFail = 0, coeffCount = 0, coeffSum = 0, maxCoeff = 0, fpSum = 0;
    std::map<std::pair<int,int>, u64> hist;
    int par[MAXN], last[MAXN + 1];
    while (true) {
      if (!next_free(a)) break;
      ++count;
      par[0] = -1; last[0] = 0;
      for (int i = 1; i < n; ++i) { par[i] = last[a[i] - 1]; last[a[i]] = i; }
      for (int v = 0; v < n; ++v) { P1[v].deg = P2[v].deg = P3[v].deg = 0; P1[v].c[0] = P2[v].c[0] = P3[v].c[0] = 1; }
      u64 d[MAXN + 1];
      for (int v = n - 1; v >= 0; --v) {
        // state polynomials of v:  A = z*P1,  B = P2 - P3,  C = P3
        Poly A, AB, ABC;
        A.deg = P1[v].deg + 1; A.c[0] = 0;
        for (int i = 0; i <= P1[v].deg; ++i) A.c[i + 1] = P1[v].c[i];
        AB.deg = A.deg; ABC.deg = A.deg;
        for (int i = 0; i <= A.deg; ++i) {
          u64 b = (i <= P2[v].deg ? P2[v].c[i] : 0) - (i <= P3[v].deg ? P3[v].c[i] : 0);
          u64 c = (i <= P3[v].deg ? P3[v].c[i] : 0);
          AB.c[i] = A.c[i] + b; ABC.c[i] = A.c[i] + b + c;
        }
        if (v == 0) { for (int i = 0; i <= n; ++i) d[i] = i <= AB.deg ? AB.c[i] : 0; break; }
        Poly Bp; Bp.deg = std::max(P2[v].deg, P3[v].deg);
        for (int i = 0; i <= Bp.deg; ++i) Bp.c[i] = (i <= P2[v].deg ? P2[v].c[i] : 0) - (i <= P3[v].deg ? P3[v].c[i] : 0);
        int p = par[v];
        mulInto(P1[p], ABC); mulInto(P2[p], AB); mulInto(P3[p], Bp);
      }
      int gam = 0; while (d[gam] == 0) ++gam;
      // maximum matching, greedy from the leaves
      bool used[MAXN]; int nu = 0;
      for (int v = 0; v < n; ++v) used[v] = false;
      for (int v = n - 1; v >= 1; --v) if (!used[v] && !used[par[v]]) { used[v] = used[par[v]] = true; ++nu; }
      int Gam = n - nu;
      bool lc = true;
      for (int j = 1; j < n; ++j) if ((u128)d[j] * d[j] < (u128)d[j - 1] * d[j + 1]) lc = false;
      if (!lc) {
        ++lcFail;
        if (lcFail <= 50) {
          fprintf(stderr, "NONLOGCONCAVE n=%d parents:", n);
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
      if (!next_rooted(a)) break;
    }
    printf("{\"n\":%d,\"free_generated\":%llu,\"free_expected\":%llu,\"logconcavity_failures\":%llu,\"unimodality_failures\":%llu,"
           "\"coefficients\":%llu,\"total_dominating_sets\":%llu,\"max_coefficient\":%llu,\"fingerprint\":\"%016llx\",\"hist\":[",
           n, count, T[n], lcFail, uniFail, coeffCount, coeffSum, maxCoeff, fpSum);
    bool first = true;
    for (auto &kv : hist) { printf("%s[%d,%d,%llu]", first ? "" : ",", kv.first.first, kv.first.second, kv.second); first = false; }
    printf("]}\n");
    fflush(stdout);
    if (count != T[n]) { fprintf(stderr, "COUNT MISMATCH at n=%d\n", n); return 3; }
  }
  return 0;
}

