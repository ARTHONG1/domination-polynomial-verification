#!/usr/bin/env python3
"""Structured families related to the Beaton--Schoonhoven trees.

T(k_1,...,k_r): a root adjacent to r hubs; the i-th hub carries k_i pendant
paths on three vertices (attached by an end vertex).  Order 1 + r + 3*sum(k_i).
T(k,k,k) is the tree T_k of Beaton and Schoonhoven.

Prints all members of order <= 40 (r <= 5) whose domination polynomial is not
log-concave, and an example of a forest whose mean number of critical vertices
jumps by more than two at a low rank.
"""
import itertools, json
from fractions import Fraction

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
    def rec(v):
        A, B, C = [0, 1], [0], [1]
        for w in children[v]:
            a, b, c = rec(w)
            A, B, C = pmul(A, padd(padd(a, b), c)), padd(pmul(B, padd(a, b)), pmul(C, a)), pmul(C, b)
        return A, B, C
    A, B, _ = rec(root)
    d = padd(A, B)
    while d and d[-1] == 0: d.pop()
    return d
def T(ks):
    ch = {0: []}; nxt = 1
    for k in ks:
        v = nxt; nxt += 1; ch[0].append(v); ch[v] = []
        for _ in range(k):
            x, y, z = nxt, nxt + 1, nxt + 2; nxt += 3
            ch[v].append(x); ch[x] = [y]; ch[y] = [z]; ch[z] = []
    return ch
def lc_failures(d):
    return [j for j in range(1, len(d) - 1) if d[j] * d[j] < d[j - 1] * d[j + 1]]
def unimodal(d):
    j = 0; n = len(d) - 1
    while j < n and d[j] <= d[j + 1]: j += 1
    while j < n and d[j] >= d[j + 1]: j += 1
    return j == n

out = {"family": []}
for r in range(1, 6):
    for ks in itertools.combinations_with_replacement(range(0, 13), r):
        n = 1 + r + 3 * sum(ks)
        if n > 40 or sum(ks) == 0: continue
        d = dom_poly(T(ks))
        assert len(d) == n + 1
        bad = lc_failures(d)
        assert unimodal(d)
        if bad:
            out["family"].append({"k": list(ks), "order": n, "failing_indices": bad,
                                  "gamma": next(i for i, x in enumerate(d) if x)})
out["family"].sort(key=lambda o: (o["order"], o["k"]))
out["T_2_3_3_coefficients"] = dom_poly(T((2, 3, 3)))

# mean jump c_{j+1}-c_j for the forest  m K_2  +  T(k,k,k)
def mean_jumps(d):
    n = len(d) - 1
    g = next(i for i, x in enumerate(d) if x)
    c = {j: Fraction(j) - Fraction((n - j + 1) * d[j - 1], d[j]) for j in range(g, n + 1)}
    return g, {j: c[j + 1] - c[j] for j in range(g, n)}
m, k = 60, 8
d = dom_poly(T((k, k, k)))
for _ in range(m): d = pmul(d, [0, 2, 1])
g, J = mean_jumps(d)
n = len(d) - 1
jmax = max(J, key=J.get)
A = (n + 2 * g + 1) // 3
out["forest_example"] = {"forest": f"{m} K_2 + T({k},{k},{k})", "order": n, "gamma": g,
                         "max_mean_jump": float(J[jmax]), "at_rank": jmax, "left_wing_end_A": A,
                         "max_mean_jump_at_ranks_ge_A": float(max(v for j, v in J.items() if j >= A)),
                         "unimodal": unimodal(d)}
print(json.dumps(out, indent=1))

