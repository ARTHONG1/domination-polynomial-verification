#!/usr/bin/env python3
"""Independent exact checks for the inequality (15) of Section 7 (the top end of Question 7.3).

Checks all labelled trees through order 7 by Prufer sequences and subset
enumeration, then random larger trees by an existing independent 3-state
domination-polynomial DP. These are finite tests, not a universal proof.
"""

import heapq
import itertools
import json
import random
import sys
from fractions import Fraction
from math import comb
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_counterexample import dompoly  # generic 3-state DP, distinct from brute


def adjacency_from_prufer(n, seq):
    deg = [1] * n
    for v in seq:
        deg[v] += 1
    leaves = [v for v in range(n) if deg[v] == 1]
    heapq.heapify(leaves)
    adj = [[] for _ in range(n)]
    for v in seq:
        u = heapq.heappop(leaves)
        adj[u].append(v)
        adj[v].append(u)
        deg[u] -= 1
        deg[v] -= 1
        if deg[v] == 1:
            heapq.heappush(leaves, v)
    u = heapq.heappop(leaves)
    v = heapq.heappop(leaves)
    adj[u].append(v)
    adj[v].append(u)
    return adj


def brute_counts(adj):
    n = len(adj)
    neighborhoods = [1 << v for v in range(n)]
    for v in range(n):
        for w in adj[v]:
            neighborhoods[v] |= 1 << w
    full = (1 << n) - 1
    d = [0] * (n + 1)
    for mask in range(1 << n):
        dominated = 0
        for v in range(n):
            if mask >> v & 1:
                dominated |= neighborhoods[v]
        if dominated == full:
            d[mask.bit_count()] += 1
    return d


def check(n, adj, d):
    degrees = [len(a) for a in adj]
    L = sum(x == 1 for x in degrees)
    leaf_counts_at_supports = [sum(degrees[w] == 1 for w in adj[v]) for v in range(n)]
    common_support_overlap = sum(comb(x, 2) for x in leaf_counts_at_supports if x >= 2)
    unshielded_degree_two = sum(degrees[v] == 2 and leaf_counts_at_supports[v] == 0 for v in range(n))
    # Exact number of bad triples in a tree. 3-neighborhoods of degree-2
    # vertices add only when they contain no leaf-neighborhood pair.
    bad_triples = L * (n - 2) - common_support_overlap + unshielded_degree_two
    assert d[n - 3] == comb(n, 3) - bad_triples
    b = comb(n, 2) - L
    u = comb(n, 3) - L * (n - 2) + comb(L, 2)
    assert d[n] == 1 and d[n - 1] == n
    assert d[n - 2] == b > 0
    assert d[n - 3] <= u
    surplus = 2 * b * (b - 1) - 3 * n * u
    factored = (n - 1 - L) * (3 * L * n - 4 * L + n * n - 2 * n) // 2
    assert surplus == factored >= 0
    actual_surplus = 2 * b * (b - 1) - 3 * n * d[n - 3]
    assert actual_surplus >= 0
    # Exact integer reformulation of c_{n-1}-c_{n-2} <= 1-2/n.
    assert 3 * n * d[n - 3] <= 2 * b * (b - 1)
    assert (actual_surplus == 0) == (L == n - 1), (n, L)
    g = next(i for i, x in enumerate(d) if x)
    for k in range(0, n - g):
        j = n - k
        pk = 1 - Fraction(d[j], comb(n, k))
        pk1 = 1 - Fraction(d[j - 1], comb(n, k + 1))
        c = j - Fraction((k + 1) * d[j - 1], d[j])
        # Exact independent expression in the missing-set failure probabilities.
        assert c == j * (pk1 - pk) / (1 - pk)
    return L == n - 1


def main():
    by_order = {}
    all_count = 0
    for n in range(3, 8):
        cnt = 0
        stars = 0
        for seq in itertools.product(range(n), repeat=n - 2):
            adj = adjacency_from_prufer(n, seq)
            d = brute_counts(adj)
            stars += check(n, adj, d)
            cnt += 1
        assert cnt == n ** (n - 2)
        by_order[str(n)] = {"labelled_trees_checked": cnt, "stars_with_equality": stars}
        all_count += cnt

    rng = random.Random(20261111)
    random_checks = 0
    for n in (8, 12, 20, 35, 60, 100):
        for _ in range(80):
            par = [-1] + [rng.randrange(v) for v in range(1, n)]
            adj = [[] for _ in range(n)]
            for v in range(1, n):
                p = par[v]
                adj[v].append(p)
                adj[p].append(v)
            check(n, adj, dompoly(par))
            random_checks += 1

    out = {
        "method": "Prufer exhaustive labelled trees & brute dominating subsets through n=7; random 3-state DP through n=100",
        "by_order": by_order,
        "labelled_checked": all_count,
        "random_dp_checked": random_checks,
        "boundary_inequality_failures": 0,
        "scope": "finite computational validation only; the proof is in Section 7 of the paper",
    }
    dest = Path(__file__).parent / "results" / "check_boundary.json"
    dest.write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(out, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
