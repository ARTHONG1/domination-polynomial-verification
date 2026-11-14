// Third completely independent verifier (no level sequences, no BH, no WROM).
// Generates rooted trees bottom-up by integer-partition multisets of smaller rooted
// tree IDs, extracts unique free trees via tree-center (leaf-peeling Jordan center,
// NOT centroid!), and computes domination polynomials via edge-cover/inclusion DP
// from scratch. Compares tree counts, total dominating sets, max coeff, log-concavity,
// unimodality, and 64-bit FNV/SplitMix multiset fingerprint for orders 2..18.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <vector>

using u64 = unsigned long long;
using u128 = __uint128_t;

struct RootedTree {
  int sz;
  std::vector<int> childIds; // nondecreasing global IDs
};

static std::vector<RootedTree> pool;
static std::vector<std::vector<int>> bySize;

static void genMultisets(int remSize, int maxSize, int minIdInMaxSize,
                         std::vector<int> &cur, std::vector<std::vector<int>> &out) {
  if (remSize == 0) {
    out.push_back(cur);
    return;
  }
  int lim = std::min(remSize, maxSize);
  for (int s = lim; s >= 1; --s) {
    const auto &ids = bySize[s];
    int startIdx = 0;
    if (s == maxSize) {
      while (startIdx < (int)ids.size() && ids[startIdx] < minIdInMaxSize) ++startIdx;
    }
    for (int idx = startIdx; idx < (int)ids.size(); ++idx) {
      cur.push_back(ids[idx]);
      genMultisets(remSize - s, s, ids[idx], cur, out);
      cur.pop_back();
    }
  }
}

static int materialize(int rtId, std::vector<std::vector<int>> &adj) {
  int me = (int)adj.size();
  adj.push_back({});
  for (int cid : pool[rtId].childIds) {
    int ch = materialize(cid, adj);
    adj[me].push_back(ch);
    adj[ch].push_back(me);
  }
  return me;
}

// AHU canonical string via sorted child encodings around Jordan center(s)
static std::vector<int> encodeSubtree(int u, int p, const std::vector<std::vector<int>> &adj) {
  std::vector<std::vector<int>> subs;
  for (int v : adj[u]) if (v != p) subs.push_back(encodeSubtree(v, u, adj));
  std::sort(subs.begin(), subs.end());
  std::vector<int> res = {1};
  for (auto &s : subs) res.insert(res.end(), s.begin(), s.end());
  res.push_back(0);
  return res;
}

static std::vector<int> jordanCenterCanon(const std::vector<std::vector<int>> &adj) {
  int n = (int)adj.size();
  std::vector<int> deg(n);
  std::vector<int> leaves;
  for (int i = 0; i < n; ++i) {
    deg[i] = (int)adj[i].size();
    if (deg[i] <= 1) leaves.push_back(i);
  }
  int rem = n;
  while (rem > 2) {
    std::vector<int> next;
    rem -= (int)leaves.size();
    for (int u : leaves) {
      for (int v : adj[u]) {
        if (--deg[v] == 1) next.push_back(v);
      }
    }
    leaves = std::move(next);
  }
  if (leaves.size() == 1) {
    return encodeSubtree(leaves[0], -1, adj);
  }
  auto c0 = encodeSubtree(leaves[0], leaves[1], adj);
  auto c1 = encodeSubtree(leaves[1], leaves[0], adj);
  if (c1 < c0) std::swap(c0, c1);
  c0.push_back(2);
  c0.insert(c0.end(), c1.begin(), c1.end());
  return c0;
}

// Independent DFS DP on arbitrary root (choose leaf-center[0])
struct States {
  std::vector<u64> inS, outCov, outUncov;
};

static States solveDFS(int u, int p, const std::vector<std::vector<int>> &adj) {
  States st{{0, 1}, {0}, {1}};
  for (int v : adj[u]) if (v != p) {
    States ch = solveDFS(v, u, adj);
    int du = (int)st.inS.size() - 1;
    int dv = (int)ch.inS.size() - 1;
    States nx{std::vector<u64>(du + dv + 1, 0),
              std::vector<u64>(du + dv + 1, 0),
              std::vector<u64>(du + dv + 1, 0)};
    auto get = [](const std::vector<u64> &vec, int idx) -> u64 {
      return idx < (int)vec.size() ? vec[idx] : 0ULL;
    };
    for (int i = 0; i <= du; ++i) {
      for (int j = 0; j <= dv; ++j) {
        u64 a = get(ch.inS, j), b = get(ch.outCov, j), c = get(ch.outUncov, j);
        nx.inS[i + j] += get(st.inS, i) * (a + b + c);
        nx.outCov[i + j] += get(st.outCov, i) * (a + b) + get(st.outUncov, i) * a;
        nx.outUncov[i + j] += get(st.outUncov, i) * b;
      }
    }
    st = std::move(nx);
  }
  return st;
}

static u64 fingerprint(const std::vector<u64> &d) {
  u64 h = 1469598103934665603ULL;
  for (u64 x : d) { h ^= x; h *= 1099511628211ULL; }
  h ^= h >> 30; h *= 0xbf58476d1ce4e5b9ULL; h ^= h >> 27; h *= 0x94d049bb133111ebULL; h ^= h >> 31;
  return h;
}

int main(int argc, char **argv) {
  int maxN = argc > 1 ? atoi(argv[1]) : 16;
  bySize.resize(maxN + 1);
  pool.push_back({1, {}});
  bySize[1].push_back(0);

  for (int n = 2; n <= maxN; ++n) {
    std::vector<int> cur;
    std::vector<std::vector<int>> ms;
    genMultisets(n - 1, n - 1, 0, cur, ms);
    for (auto &m : ms) {
      int id = (int)pool.size();
      pool.push_back({n, m});
      bySize[n].push_back(id);
    }

    std::set<std::vector<int>> seenFree;
    u64 lcFail = 0, uniFail = 0, coeffSum = 0, maxCoeff = 0, fpSum = 0;
    for (int id : bySize[n]) {
      // Quick pre-filter: only materialize if max child subtree size <= n/2 (centroid)
      int maxCh = pool[id].childIds.empty() ? 0 : pool[pool[id].childIds[0]].sz;
      if (2 * maxCh > n) continue;
      std::vector<std::vector<int>> adj;
      materialize(id, adj);
      auto key = jordanCenterCanon(adj);
      if (!seenFree.insert(key).second) continue;

      States rootSt = solveDFS(n - 1, -1, adj); // intentionally root at n-1 (non-centroid!)
      std::vector<u64> d(n + 1, 0);
      for (int j = 0; j <= n; ++j) {
        u64 a = j < (int)rootSt.inS.size() ? rootSt.inS[j] : 0;
        u64 b = j < (int)rootSt.outCov.size() ? rootSt.outCov[j] : 0;
        d[j] = a + b;
        coeffSum += d[j];
        if (d[j] > maxCoeff) maxCoeff = d[j];
      }
      for (int j = 1; j < n; ++j) {
        if ((u128)d[j] * d[j] < (u128)d[j - 1] * d[j + 1]) ++lcFail;
      }
      int j = 0;
      while (j < n && d[j] <= d[j + 1]) ++j;
      while (j < n && d[j] >= d[j + 1]) ++j;
      if (j != n) ++uniFail;
      fpSum += fingerprint(d);
    }
    printf("{\"n\":%d,\"rooted\":%zu,\"free\":%zu,\"lcFail\":%llu,\"uniFail\":%llu,\"totalDom\":%llu,\"maxCoeff\":%llu,\"fingerprint\":\"%016llx\"}\n",
           n, bySize[n].size(), seenFree.size(), lcFail, uniFail, coeffSum, maxCoeff, fpSum);
  }
  return 0;
}

