#!/usr/bin/env python3
"""Independent check of the negative answer to Question 7.2.

Builds the tree W(k1,k2,k3;M) explicitly (parent array), computes the complete
domination polynomial with the generic three-state tree recurrence (sequential
child merging, exact integers, no closed formula), and tests the integer form
of c_{j+1}-c_j <= 2:
    (n-j+1) d_{j-1} d_{j+1} <= d_j d_{j+1} + (n-j) d_j^2     (gamma < j < n).
The recurrence code is first validated against subset enumeration on small
members of the family and on random trees."""
import json, random, sys
from fractions import Fraction
from pathlib import Path

def build(ks, M):
    par = [-1]
    def add(p): par.append(p); return len(par) - 1
    for k in ks:
        h = add(0)
        for _ in range(k):
            v = h
            for _ in range(3): v = add(v)
    for _ in range(M):
        add(add(0))
    return par

def dompoly(par):
    n = len(par)
    A = [[0, 1] for _ in range(n)]; B = [[0] for _ in range(n)]; C = [[1] for _ in range(n)]
    def mul(a, b):
        r = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b): r[i + j] += x * y
        return r
    def add(a, b):
        if len(a) < len(b): a, b = b, a
        r = a[:]
        for i, y in enumerate(b): r[i] += y
        return r
    for w in range(n - 1, 0, -1):               # children have larger indices
        v = par[w]
        aw, bw, cw = A[w], B[w], C[w]
        ab = add(aw, bw); abc = add(ab, cw)
        na = mul(A[v], abc)
        nb = add(mul(B[v], ab), mul(C[v], aw))
        nc = mul(C[v], bw)
        A[v], B[v], C[v] = na, nb, nc
        A[w] = B[w] = C[w] = None
    d = add(A[0], B[0])
    return d + [0] * (n + 1 - len(d))

def brute(par):
    n = len(par); nb = [1 << v for v in range(n)]
    for v in range(1, n): nb[v] |= 1 << par[v]; nb[par[v]] |= 1 << v
    full = (1 << n) - 1; cnt = [0] * (n + 1)
    dm = [0] * (1 << n)
    for s in range(1, 1 << n):
        low = (s & -s).bit_length() - 1
        dm[s] = dm[s & (s - 1)] | nb[low]
        if dm[s] == full: cnt[bin(s).count('1')] += 1
    return cnt

def independence(par):
    n = len(par); a1 = [1] * n; a0 = [0] * n
    for w in range(n - 1, 0, -1):
        v = par[w]; a1[v] += a0[w]; a0[v] += max(a0[w], a1[w])
    return max(a0[0], a1[0])

def analyse(ks, M):
    par = build(ks, M); n = len(par); d = dompoly(par)
    assert d[n] == 1 and sum(d) > 0
    g = next(j for j, x in enumerate(d) if x)
    assert all(d[j] > 0 for j in range(g, n + 1))
    viol = [j for j in range(g + 1, n)
            if (n - j + 1) * d[j - 1] * d[j + 1] > d[j] * d[j + 1] + (n - j) * d[j] * d[j]]
    jumps = {j: float(1 + Fraction((n - j + 1) * d[j - 1], d[j]) - Fraction((n - j) * d[j], d[j + 1])) for j in viol}
    i = 0
    while i < n and d[i] <= d[i + 1]: i += 1
    peak = i
    while i < n and d[i] >= d[i + 1]: i += 1
    lc = [j for j in range(1, n) if d[j] * d[j] < d[j - 1] * d[j + 1]]
    Gam = independence(par)
    return {'ks': list(ks), 'M': M, 'n': n, 'gamma': g, 'Gamma': Gam, 'gap': Gam - g,
            'd_gamma': str(d[g]), 'd_gamma+1': str(d[g + 1]), 'd_gamma+2': str(d[g + 2]),
            'jump_violations_j': viol, 'jump_values': jumps, 'unimodal': i == n, 'peak': peak,
            'logconcavity_failures_j': lc}

if __name__ == '__main__':
    random.seed(7)
    checked = 0
    for ks, M in [((1, 1, 2), 2), ((2, 1), 3), ((1, 1, 1), 4), ((2, 2), 1), ((1, 2, 1), 0)]:
        p = build(ks, M); assert dompoly(p) == brute(p), (ks, M); checked += 1
    for _ in range(300):
        n = random.randint(2, 16); p = [-1] + [random.randrange(v) for v in range(1, n)]
        assert dompoly(p) == brute(p); checked += 1
    print('recurrence validated against subset enumeration on', checked, 'trees')
    out = []
    for ks, M in [((8, 8, 9), 3211), ((8, 8, 9), 3210), ((9, 9, 9), 7700)]:
        r = analyse(ks, M); out.append(r)
        print({k: v for k, v in r.items() if not k.startswith('d_')})
    Path(__file__).with_name('verify_result.json').write_text(json.dumps(out, indent=1) + '\n')

