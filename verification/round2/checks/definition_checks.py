#!/usr/bin/env python3
"""Definition-based finite tests of the statements of Sections 2-5.

Input: the mathematical definitions in the fixed submitted main.tex.
Run: python3 definition_checks.py   (Python >= 3.10)
Output: DEFINITION_CHECKS.json next to this file.

Does not import or depend on submitted computation code or earlier verification.
Enumerates all labelled simple graphs with 0..5 vertices and additionally
all labelled forests on six vertices, including disconnected and isolated.
"""
from __future__ import annotations

import itertools
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent


def graph(n: int, bits: int):
    E = tuple(itertools.combinations(range(n), 2))
    adj = [0] * n
    parent = list(range(n))
    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v
    forest = True
    for i, (a, b) in enumerate(E):
        if bits >> i & 1:
            adj[a] |= 1 << b
            adj[b] |= 1 << a
            ra, rb = root(a), root(b)
            if ra == rb:
                forest = False
            else:
                parent[ra] = rb
    color = [-1] * n
    bipartite = True
    for v in range(n):
        if color[v] != -1:
            continue
        color[v] = 0
        queue = [v]
        for u in queue:
            for w in range(n):
                if not (adj[u] >> w & 1):
                    continue
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    queue.append(w)
                elif color[w] == color[u]:
                    bipartite = False
    return adj, forest, bipartite


def evaluate(n, adj, forest, bipartite, cnt):
    allmask = (1 << n) - 1
    closed = [adj[v] | (1 << v) for v in range(n)]
    dom = []
    indep = []
    for m in range(1 << n):
        covered = 0
        for v in range(n):
            if m >> v & 1:
                covered |= closed[v]
        if covered == allmask:
            dom.append(m)
        if all(not (adj[v] & m) for v in range(n) if m >> v & 1):
            indep.append(m)
    ds = set(dom)
    crit = {m:sum(1 for v in range(n) if m >> v & 1 and (m ^ (1 << v)) not in ds) for m in dom}
    minimal = [m for m in dom if crit[m] == m.bit_count()]
    assert minimal
    gamma = min(m.bit_count() for m in dom)
    Gamma = max(m.bit_count() for m in minimal)
    alpha = max(m.bit_count() for m in indep)
    H = Gamma - gamma
    d = [sum(m.bit_count() == j for m in dom) for j in range(n + 1)]
    assert all((d[j] > 0) == (gamma <= j <= n) for j in range(n + 1))
    cnt['support'] += 1
    for m in dom:
        for u in dom:
            if m & u == m:
                for v in range(n):
                    if u >> v & 1 and (u ^ (1 << v)) not in ds:
                        assert m >> v & 1 and (m ^ (1 << v)) not in ds
                cnt['critical_monotonicity_pairs'] += 1
    for j in range(1, n + 1):
        lhs = (n - j + 1) * d[j - 1]
        rhs = sum(j - crit[m] for m in dom if m.bit_count() == j)
        assert lhs == rhs
        cnt['incidence'] += 1
    if forest:
        assert all(m.bit_count() + crit[m] >= 2 * gamma for m in dom)
        cnt['forest_lower_bound'] += 1
        assert all(2 * gamma - m.bit_count() <= crit[m] <= 2 * Gamma - m.bit_count() for m in dom)
        cnt['forest_two_sided'] += 1
    if bipartite:
        assert all(m.bit_count() + crit[m] <= 2 * alpha for m in dom)
        assert Gamma == alpha
        cnt['bipartite_upper_bound'] += 1
    if not any(a == 0 for a in adj):
        assert n >= gamma + Gamma
        cnt['ore'] += 1
    for j in range(1, n + 1):
        if forest and 3*j <= n+2*gamma+1:
            assert d[j-1] <= d[j]
            cnt['forest_increasing_segment'] += 1
        if bipartite and 3*j >= n+2*alpha+1:
            assert d[j-1] >= d[j]
            cnt['bipartite_decreasing_segment'] += 1
    avd = Fraction(sum(m.bit_count() for m in dom), len(dom))
    if forest:
        assert avd >= Fraction(n+2*gamma,3)
        cnt['forest_avd'] += 1
    if bipartite:
        assert avd <= Fraction(n+2*alpha,3)
        cnt['bipartite_avd'] += 1
    if n == 0:
        assert gamma == Gamma == alpha == 0 and d == [1]
        cnt['empty_graph'] += 1
        return
    means={}
    vars={}
    for j in range(gamma,n+1):
        scores=[crit[m] for m in dom if m.bit_count()==j]
        c=Fraction(sum(scores),len(scores))
        v=sum((Fraction(x)-c)**2 for x in scores)/len(scores)
        means[j]=c
        vars[j]=v
        assert (j-c)*d[j]==(n-j+1)*d[j-1]
        cnt['mean_identity'] += 1
        if j>gamma:
            assert (j-c)*(c-means[j-1])<=v
            cnt['covariance'] += 1
    for j in range(gamma+1,n):
        if d[j-1]>=d[j]<d[j+1]:
            assert means[j+1]-means[j]>2
            cnt['valley'] += 1
    if forest:
        K=((H+1)**2+3)//4
        for j in range(gamma+K,n+1):
            assert means[j]-means[j-1]<=2
            cnt['forest_jump_bound'] += 1
        if n-gamma>=3*K-7:
            assert is_unimodal(d)
            cnt['general_Hh_criterion'] += 1
        if not is_unimodal(d) and not any(a==0 for a in adj):
            assert H>=3 and n<=6*K-H-16
        if not any(a==0 for a in adj) and 3*H*H+4*H-19<=2*n:
            assert is_unimodal(d)
            cnt['general_forest_criterion_iii'] += 1
        if H<=3:
            assert is_unimodal(d)
            cnt['gap_le3_forest'] += 1


def is_unimodal(d):
    i=0
    while i+1<len(d) and d[i]<=d[i+1]:
        i+=1
    return all(d[j]>=d[j+1] for j in range(i,len(d)-1))


def main():
    cnt=Counter()
    census={}
    for n in range(7):
        num_edges=n*(n-1)//2
        total=0
        forests=0
        for bits in range(1<<num_edges):
            adj,forest,bipartite=graph(n,bits)
            if n==6 and not forest:
                continue
            evaluate(n,adj,forest,bipartite,cnt)
            total+=1
            forests+=int(forest)
        census[str(n)]={'graphs_tested':total,'forests_tested':forests,
                         'scope':'all labelled graphs' if n<=5 else 'all labelled forests only'}
    assert sum(x['graphs_tested'] for x in census.values())>1000
    out={'method':'fresh exhaustive subset-based definitions, independent of submitted generators and DP',
         'by_order':census,'checks':dict(cnt),'all_passed':True,
         'scope':'finite definition-based test'}
    (HERE/'DEFINITION_CHECKS.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
    print('DEFINITION_CHECKS_OK',sum(x['graphs_tested'] for x in census.values()),'graphs / forests',dict(cnt))

if __name__=='__main__':
    main()
