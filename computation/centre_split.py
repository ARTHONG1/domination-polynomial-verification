#!/usr/bin/env python3
"""Splits the first coefficients of D(T,x) according to whether the dominating
set contains the centre v_0 (Remark 6.7 of the paper).

T(k_1,...,k_r; tail): centre v_0 with hubs v_1..v_r, k_i pendant paths on three
vertices at v_i, and a pendant path on 'tail' vertices at v_0.
U = T(2,2,3; 2).
"""
import json
from pathlib import Path

def padd(a, b):
    r = [0] * max(len(a), len(b))
    for i, x in enumerate(a): r[i] += x
    for i, x in enumerate(b): r[i] += x
    return r
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return r
def state_polys(children, root=0):
    """A: root in S;  B: root not in S but dominated (see Appendix A)."""
    def rec(v):
        A, B, C = [0, 1], [0], [1]
        for w in children[v]:
            a, b, c = rec(w)
            A, B, C = pmul(A, padd(padd(a, b), c)), padd(pmul(B, padd(a, b)), pmul(C, a)), pmul(C, b)
        return A, B, C
    A, B, _ = rec(root)
    return A, B
def tree(ks, tail=0):
    ch = {0: []}; n = 1
    for k in ks:
        v = n; n += 1; ch[0].append(v); ch[v] = []
        for _ in range(k):
            x, y, z = n, n + 1, n + 2; n += 3
            ch[v].append(x); ch[x] = [y]; ch[y] = [z]; ch[z] = []
    p = 0
    for _ in range(tail):
        ch[p].append(n); ch[n] = []; p = n; n += 1
    return ch

out = []
for name, ks, tail in [("T(2,2,3)", (2, 2, 3), 0), ("U = T(2,2,3) with a pendant P_2 at v_0", (2, 2, 3), 2),
                       ("T(2,2,2) with a pendant P_2 at v_0", (2, 2, 2), 2), ("T(2,3,3)", (2, 3, 3), 0)]:
    A, B = state_polys(tree(ks, tail))
    d = padd(A, B)
    g = next(i for i, x in enumerate(d) if x)
    at = lambda p, i: p[i] if i < len(p) else 0
    out.append({"tree": name, "order": len(d) - 1, "gamma": g,
                "with_centre": [at(A, g + i) for i in range(3)],
                "without_centre": [at(B, g + i) for i in range(3)],
                "d_gamma..d_gamma+2": d[g:g + 3],
                "d1_squared": d[g + 1] ** 2, "d0_times_d2": d[g] * d[g + 2],
                "logconcave_at_gamma_plus_1": d[g + 1] ** 2 >= d[g] * d[g + 2]})
here = Path(__file__).resolve().parent
(here / "results" / "centre_split.json").write_text(json.dumps(out, indent=1) + "\n")
for o in out: print(o)

