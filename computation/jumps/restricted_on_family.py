#!/usr/bin/env python3
"""The weaker inequality (only for j >= A+1, A = floor((n+2*gamma+1)/3)) on the trees that
refute Question 7.2 and on further members of the family; complete polynomials, exact tests."""
import json, sys
from fractions import Fraction as Fr
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from verify_counterexample import build, dompoly
out = []
for ks, M in [((8, 8, 9), 3211), ((9, 9, 9), 7700), ((6, 6, 6, 6), 700), ((5, 5, 5, 5, 5), 300), ((10, 10, 10), 2500)]:
    par = build(ks, M); n = len(par); d = dompoly(par)
    g = next(j for j, x in enumerate(d) if x); A = (n + 2 * g + 1) // 3
    J = lambda j: 1 + Fr((n - j + 1) * d[j - 1], d[j]) - Fr((n - j) * d[j], d[j + 1])
    viol_all = [j for j in range(g + 1, n) if J(j) > 2]
    rj = max(range(max(A + 1, g + 1), n), key=J)
    i = 0
    while i < n and d[i] <= d[i + 1]: i += 1
    while i < n and d[i] >= d[i + 1]: i += 1
    row = {'ks': list(ks), 'M': M, 'n': n, 'gamma': g, 'A': A, 'violations_all_j': viol_all,
           'max_jump_all': float(max(J(j) for j in range(g + 1, n))),
           'max_jump_restricted': float(J(rj)), 'argmax_restricted': rj, 'unimodal': i == n}
    out.append(row); print(row, flush=True)
Path(__file__).with_name('restricted_on_family.json').write_text(json.dumps(out, indent=1) + '\n')

