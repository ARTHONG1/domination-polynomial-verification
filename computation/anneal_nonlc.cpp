// Heuristic search (simulated annealing over trees of a fixed order) for a tree
// whose domination polynomial is NOT log-concave.  A hit is an exact witness;
// the absence of hits proves nothing.
// Usage: anneal_nonlc N SEED ITERATIONS [MODE [TARGET]]
//   MODE 0 (default): minimise min_j log(d_j^2/(d_{j-1}d_{j+1})); hit = exact log-concavity failure
//   MODE 1: maximise max_j (c_{j+1}-c_j); hit = value above TARGET (floating point; re-check exactly)
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>
typedef unsigned long long u64;
typedef __uint128_t u128;
static const int MAXN = 62;
static int n, par[MAXN], ord[MAXN];
static std::vector<int> ch[MAXN];
static u64 A[MAXN][MAXN + 1], B[MAXN][MAXN + 1], C[MAXN][MAXN + 1], d[MAXN + 1];
static int dg[MAXN];

static void poly() {
  for (int v = 0; v < n; ++v) ch[v].clear();
  for (int v = 1; v < n; ++v) ch[par[v]].push_back(v);
  int k = 0; ord[k++] = 0;
  for (int i = 0; i < k; ++i) for (int w : ch[ord[i]]) ord[k++] = w;
  for (int v = 0; v < n; ++v) { for (int j = 0; j <= n; ++j) A[v][j] = B[v][j] = C[v][j] = 0; A[v][1] = 1; C[v][0] = 1; dg[v] = 1; }
  u64 na[MAXN + 1], nb[MAXN + 1], nc[MAXN + 1];
  for (int t = n - 1; t >= 1; --t) {
    int w = ord[t], v = par[w], dv = dg[v], dw = dg[w];
    for (int j = 0; j <= dv + dw; ++j) na[j] = nb[j] = nc[j] = 0;
    for (int i = 0; i <= dv; ++i) for (int j = 0; j <= dw; ++j) {
      u64 aw = A[w][j], bw = B[w][j], cw = C[w][j];
      na[i + j] += A[v][i] * (aw + bw + cw);
      nb[i + j] += B[v][i] * (aw + bw) + C[v][i] * aw;
      nc[i + j] += C[v][i] * bw;
    }
    dg[v] = dv + dw;
    for (int j = 0; j <= dg[v]; ++j) { A[v][j] = na[j]; B[v][j] = nb[j]; C[v][j] = nc[j]; }
  }
  for (int j = 0; j <= n; ++j) d[j] = A[0][j] + B[0][j];
}
// objective: min over internal indices of log(d_j^2 / (d_{j-1} d_{j+1})); negative <=> not log-concave
static int MODE = 0;   // 0: log-concavity ratio, 1: negative of the largest mean jump c_{j+1}-c_j
static double TARGET = 1.0;
static double objective(bool &exactFail) {
  poly();
  double best = 1e9; exactFail = false;
  if (MODE == 1) {
    int g = 0; while (d[g] == 0) ++g;
    double mx = -1e9;
    for (int q = g; q < n; ++q) {
      double J = 1.0 + (double)(n - q + 1) * (double)d[q - 1] / (double)d[q] - (double)(n - q) * (double)d[q] / (double)d[q + 1];
      if (J > mx) mx = J;
    }
    exactFail = mx > TARGET;
    return -mx;
  }
  for (int j = 1; j < n; ++j) {
    if (d[j - 1] == 0 || d[j + 1] == 0) continue;
    double r = 2 * std::log((double)d[j]) - std::log((double)d[j - 1]) - std::log((double)d[j + 1]);
    if (r < best) best = r;
    if ((u128)d[j] * d[j] < (u128)d[j - 1] * d[j + 1]) exactFail = true;
  }
  return best;
}
static bool inSubtree(int u, int v) { while (u != -1) { if (u == v) return true; u = par[u]; } return false; }

int main(int argc, char **argv) {
  n = atoi(argv[1]); u64 seed = strtoull(argv[2], 0, 10); long iters = atol(argv[3]);
  if (argc > 4) MODE = atoi(argv[4]);
  if (argc > 5) TARGET = atof(argv[5]);
  std::mt19937_64 rng(seed);
  par[0] = -1;
  for (int v = 1; v < n; ++v) par[v] = (int)(rng() % v);
  bool fail; double cur = objective(fail), bestSeen = cur;
  std::uniform_real_distribution<double> U(0, 1);
  for (long it = 0; it < iters && !fail; ++it) {
    double temp = 0.05 * (1.0 - (double)it / iters) + 0.002;
    int v = 1 + (int)(rng() % (n - 1)), u = (int)(rng() % n);
    if (u == par[v] || inSubtree(u, v)) continue;
    int old = par[v]; par[v] = u;
    bool f2; double nw = objective(f2);
    if (nw <= cur || U(rng) < std::exp((cur - nw) / temp)) { cur = nw; fail = f2; if (cur < bestSeen) bestSeen = cur; }
    else par[v] = old;
  }
  if (fail) {
    objective(fail);
    printf("{\"n\":%d,\"seed\":%llu,\"mode\":%d,\"hit\":true,\"objective\":%.6f,\"parents\":[", n, seed, MODE, cur);
    for (int v = 1; v < n; ++v) printf("%s%d", v > 1 ? "," : "", par[v]);
    printf("],\"coefficients\":[");
    for (int j = 0; j <= n; ++j) printf("%s%llu", j ? "," : "", d[j]);
    printf("]}\n");
  } else printf("{\"n\":%d,\"seed\":%llu,\"mode\":%d,\"hit\":false,\"best_objective\":%.6f}\n", n, seed, MODE, bestSeen);
  return 0;
}


