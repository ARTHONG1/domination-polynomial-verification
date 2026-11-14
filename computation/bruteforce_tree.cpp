// Exhaustive enumeration of all vertex subsets of one tree (order <= 32):
// prints the number of dominating sets of each size.  No recurrence is used.
// Usage: bruteforce_tree p_1 p_2 ... p_{n-1}   (p_i = parent of vertex i, root 0)
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
int main(int argc, char **argv) {
  int n = argc;                       // vertices 0..n-1
  if (n < 2 || n > 32) { fprintf(stderr, "order must be 2..32\n"); return 1; }
  std::vector<uint32_t> nb(n);
  for (int v = 0; v < n; ++v) nb[v] = 1u << v;
  for (int v = 1; v < n; ++v) {
    int p = atoi(argv[v]);
    if (p < 0 || p >= v) { fprintf(stderr, "parents must precede children\n"); return 1; }
    nb[v] |= 1u << p; nb[p] |= 1u << v;
  }
  int lo = n / 2, hi = n - lo;
  std::vector<uint32_t> L((size_t)1 << lo), H((size_t)1 << hi);
  L[0] = 0; H[0] = 0;
  for (uint32_t s = 1; s < (1u << lo); ++s) L[s] = L[s & (s - 1)] | nb[__builtin_ctz(s)];
  for (uint32_t s = 1; s < (1u << hi); ++s) H[s] = H[s & (s - 1)] | nb[lo + __builtin_ctz(s)];
  uint32_t full = n == 32 ? 0xffffffffu : ((1u << n) - 1);
  std::vector<unsigned long long> cnt(n + 1, 0);
  for (uint32_t h = 0; h < (1u << hi); ++h) {
    uint32_t dh = H[h]; int ph = __builtin_popcount(h);
    for (uint32_t l = 0; l < (1u << lo); ++l)
      if ((dh | L[l]) == full) cnt[ph + __builtin_popcount(l)]++;
  }
  for (int j = 0; j <= n; ++j) printf("%s%llu", j ? " " : "", cnt[j]);
  printf("\n");
  return 0;
}

