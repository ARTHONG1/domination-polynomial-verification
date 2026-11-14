#!/usr/bin/env python3
"""Sharpness of  c_{j+1}-c_j < 2(j-gamma)+1  for trees.

W_r(k;M): centre v0, r hubs each carrying k pendant 3-vertex paths, M pendant 2-vertex
paths at v0.  n = 1+r+3rk+2M, gamma = 1+rk+M,
   D(x) = x^(M+rk) [ (2+x)^M (x f^r + g^r) - w^r ],
   f = x((x+1)(x+2))^k + (x^2+3x+1)^k,  g = f-(x+1)^k,  w = (x^2+3x+1)^k-(x+1)^k.
We divide by 2^M and use exact rationals.  The term w^r/2^M lies in [0,1) coefficientwise for
the single coefficient where it matters, so replacing it by 0 and by 1 gives rigorous upper
and lower bounds for d_{gamma+r-1}/2^M, hence a rigorous LOWER bound for the jump at
j = gamma+r-2 (reported below).  With M = 2^(k + ceil(k/(2(r-1)))) the jump tends to 2r-3."""
import json, sys
from fractions import Fraction as Fr
from math import comb
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from family_low import pmul, ppow, padd, psub, shift
from verify_counterexample import build, dompoly

def parts(r, k, T):
    q, p, s = [2, 3, 1], [1, 3, 1], [1, 1]
    qk, pk, sk = ppow(q, k, T), ppow(p, k, T), ppow(s, k, T)
    f = padd(shift(qk, 1, T), pk); g = psub(f, sk); w = psub(pk, sk)
    return padd(shift(ppow(f, r, T), 1, T), ppow(g, r, T)), ppow(w, r, T)

def exact_low(r, k, M, T):
    inner, wr = parts(r, k, T)
    return psub(pmul([comb(M, i) * 2 ** (M - i) for i in range(T + 1)], inner, T), wr)

def jump_lower(r, k, M):
    t = r - 2; T = r + 1
    inner, wr = parts(r, k, T)
    sc = pmul([Fr(comb(M, i), 2 ** i) for i in range(T + 1)], inner, T)   # = (D~ + w^r)/2^M
    assert all(x == 0 for x in wr[:r]) and wr[r] == (2 * k) ** r and wr[r].bit_length() <= M
    n = 1 + r + 3 * r * k + 2 * M; g = 1 + r * k + M; j = g + t
    dm1, d0 = sc[t], sc[t + 1]             # d_{j-1}/2^M, d_j/2^M  (exact: indices < r)
    d1_low = sc[t + 2] - 1                 # d_{j+1}/2^M >= this
    e_j = Fr(n - j + 1) * dm1 / d0
    e_j1_up = Fr(n - j) * d0 / d1_low
    return n, float(e_j), float(e_j1_up), float(1 + e_j - e_j1_up)

if __name__ == '__main__':
    for r, k, M in [(3, 2, 7), (4, 2, 9), (4, 3, 11), (5, 2, 11), (3, 3, 40)]:
        par = build((k,) * r, M); d = dompoly(par); g = 1 + r * k + M
        Dl = exact_low(r, k, M, 8)
        assert Dl[0] == 0 and [d[g + i] for i in range(8)] == Dl[1:9], (r, k, M)
        n = len(par); j = g + r - 2
        ex = 1 + Fr((n - j + 1) * d[j - 1], d[j]) - Fr((n - j) * d[j], d[j + 1])
        assert jump_lower(r, k, M)[3] <= float(ex) + 1e-12
    print('closed formula = generic recurrence on 5 explicit trees; lower bounds consistent')
    rows = []
    for r in (3, 4, 5):
        for k in (8, 12, 16, 24, 32, 48, 64, 96, 128):
            M = 2 ** (k + -(-k // (2 * (r - 1))))
            n, e0, e1, J = jump_lower(r, k, M)
            rows.append({'r': r, 't': r - 2, 'k': k, 'log2_M': M.bit_length() - 1, 'e_j': e0, 'e_j+1_upper': e1,
                         'jump_lower_bound': J, 'limit_2t+1': 2 * r - 3})
            print('r=%d t=%d k=%3d log2M=%3d  e_j=%.6f  e_j+1<=%.2e  jump>=%.6f  (limit %d)' % (r, r - 2, k, M.bit_length() - 1, e0, e1, J, 2 * r - 3))
    Path(__file__).with_name('sharpness_table.json').write_text(json.dumps(rows, indent=1) + '\n')

