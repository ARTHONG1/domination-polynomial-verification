#!/usr/bin/env python3
"""Post-processing of the outputs of Program I (independent_check.cpp).

  1. Recounts, by an Euler-transform argument that never enumerates a forest,
     the forests without isolated vertices with upper domination gap four and
     n - gamma <= 13 (Remark 6.4 of the paper).  Input: the joint distribution
     of (order, n - gamma, Gamma - gamma) over all trees of order 2..22.
  2. Evaluates the trees T_k = T(k,k,k) of Beaton and Schoonhoven (order 9k+4)
     and compares d_gamma and d_{gamma+1} with the values proved in their paper,
     as a sanity check of the recurrence against a published statement.

Usage: python3 analyze.py        (reads results/program1_order_*.jsonl)
"""
import glob, json, sys
from math import comb
from pathlib import Path

here = Path(__file__).resolve().parent
hist = {}
for f in sorted(glob.glob(str(here / "results" / "program1_order_*.jsonl"))):
    for line in open(f):
        if line.strip():
            o = json.loads(line)
            if o["n"] <= 22:
                h = hist.setdefault(o["n"], {})
                for m, g, c in o["hist"]:
                    h[(m, g)] = h.get((m, g), 0) + c
assert sorted(hist) == list(range(2, 23)), "orders 2..22 required"
summary = {"trees_of_order_2_to_22": sum(sum(h.values()) for h in hist.values())}

# --- forests = multisets of trees of order >= 2 -------------------------------
NMAX, MMAX, H = 22, 13, 4
poly = {(0, 0, 0): 1}
for n in sorted(hist):
    for (m, h), c in sorted(hist[n].items()):
        new = {}
        for (N, M, G), val in poly.items():
            k = 0
            while N + k * n <= NMAX and M + k * m <= MMAX and G + k * h <= H:
                key = (N + k * n, M + k * m, G + k * h)
                new[key] = new.get(key, 0) + val * comb(c + k - 1, k)
                k += 1
        poly = new
by_order = {}
for (N, M, G), val in poly.items():
    if G == H:
        by_order[N] = by_order.get(N, 0) + val
summary["gap4_forests_with_n_minus_gamma_le_13"] = sum(by_order.values())
summary["gap4_forests_by_order"] = {str(k): by_order[k] for k in sorted(by_order)}

# --- Beaton--Schoonhoven trees T_k ------------------------------------------
def padd(a, b):
    r = [0] * max(len(a), len(b))
    for i, x in enumerate(a): r[i] += x
    for i, x in enumerate(b): r[i] += x
    return r
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): r[i + j] += x * y
    return r
def dom_poly(children, root=0):
    sys.setrecursionlimit(10000)
    def rec(v):
        A, B, C = [0, 1], [0], [1]
        for w in children[v]:
            a, b, c = rec(w)
            A, B, C = pmul(A, padd(padd(a, b), c)), padd(pmul(B, padd(a, b)), pmul(C, a)), pmul(C, b)
        return A, B, C
    A, B, _ = rec(root)
    return padd(A, B)
def T(k):
    ch = {0: []}
    nxt = 1
    for _ in range(3):
        v = nxt; nxt += 1; ch[0].append(v); ch[v] = []
        for _ in range(k):
            x, y, z = nxt, nxt + 1, nxt + 2; nxt += 3
            ch[v].append(x); ch[x] = [y]; ch[y] = [z]; ch[z] = []
    return ch
bs = []
for k in range(1, 9):
    d = dom_poly(T(k))
    n = 9 * k + 4
    assert all(x == 0 for x in d[n + 1:])
    bad = [j for j in range(1, n) if d[j] * d[j] < d[j - 1] * d[j + 1]]
    j = 0
    while j < n and d[j] <= d[j + 1]: j += 1
    while j < n and d[j] >= d[j + 1]: j += 1
    g = next(i for i, x in enumerate(d) if x)
    assert d[g] == 1 and g == 3 * k + 1 and d[g + 1] == 9 * k + 3 * 2 ** k   # values proved in [BS]
    bs.append({"k": k, "order": n, "gamma": g, "d_gamma": d[g], "d_gamma_plus_1": d[g + 1],
               "logconcave": not bad, "failing_indices": bad, "unimodal": j == n})
summary["beaton_schoonhoven_trees"] = bs
(here / "results" / "gap4_boundary_and_BS_trees.json").write_text(json.dumps(summary, indent=1) + "\n")
print(json.dumps({k: v for k, v in summary.items() if k != "beaton_schoonhoven_trees"}, indent=1))
print("T_k log-concave:", {b["k"]: b["logconcave"] for b in bs})

