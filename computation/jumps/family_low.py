"""Exact search in the family W(k1,k2,k3; M): T(k1,k2,k3) with M pendant P2's at v0.
Only the three lowest coefficients are needed for the jump at j = gamma+1."""
from fractions import Fraction
from math import comb
import sys

def pmul(a, b, T):
    r = [0]*(T+1)
    for i, x in enumerate(a):
        if x == 0 or i > T: continue
        for j, y in enumerate(b):
            if i+j > T: break
            r[i+j] += x*y
    return r
def ppow(a, n, T):
    r = [1]+[0]*T
    base = a[:T+1] + [0]*max(0, T+1-len(a))
    while n:
        if n & 1: r = pmul(r, base, T)
        base = pmul(base, base, T); n >>= 1
    return r
def padd(a, b): return [x+y for x, y in zip(a, b)]
def psub(a, b): return [x-y for x, y in zip(a, b)]
def shift(a, s, T): return ([0]*s + a)[:T+1]

def low(ks, M, T=4):
    """coefficients of D / x^(M+sum(ks)+1), degrees 0..T-? (exact for 0..T-2)"""
    q, r, s = [2,3,1], [1,3,1], [1,1]
    F = [1]+[0]*T; G = [1]+[0]*T; W = [1]+[0]*T
    for k in ks:
        qk, rk, sk = ppow(q,k,T), ppow(r,k,T), ppow(s,k,T)
        f = padd(shift(qk,1,T), rk)            # (x q^k + r^k)
        g = psub(f, sk)                        # valuation 1
        w = psub(rk, sk)                       # valuation 1
        F = pmul(F, f, T); G = pmul(G, g, T); W = pmul(W, w, T)
    r3 = len(ks)
    tails = [comb(M,i)*2**(M-i) for i in range(T+1)]
    # D/x^(M+K) = (2+x)^M [x F + G] - W ;  with G, W of valuation r3
    inner = padd(shift(F,1,T), G)
    D = psub(pmul(tails, inner, T), W)
    return D   # D[1] = d_gamma, D[2] = d_{gamma+1}, ... (when r3 >= 2)

def jump(ks, M):
    D = low(ks, M, 5)
    assert D[0] == 0 and D[1] > 0
    n = 1 + len(ks) + 3*sum(ks) + 2*M
    g = M + sum(ks) + 1
    dg, d1, d2 = D[1], D[2], D[3]
    j = g+1
    lhs = (n-j+1)*dg*d2
    rhs = d1*d2 + (n-j)*d1*d1
    val = 1 + Fraction((n-j+1)*dg, d1) - Fraction((n-j)*d1, d2)
    return n, g, float(val), lhs > rhs

if __name__ == '__main__':
    for k in (8, 9, 10, 12):
        best = None
        for M in range(200, 40001, 100):
            n, g, v, bad = jump((k,k,k), M)
            if best is None or v > best[2]: best = (M, n, v, bad)
        print('k', k, 'best M', best)

