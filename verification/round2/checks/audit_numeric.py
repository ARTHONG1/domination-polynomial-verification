#!/usr/bin/env python3
"""Independent exact-integer audit of the submitted paper's numeric claims.

The two W polynomial paths use (a) the paper's symbolic factors and
(b) independently built, three-state rooted-subtree dynamic programming.
Neither imports the submitted supplementary computation programs.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def add(a, b):
    c = [0] * max(len(a), len(b))
    for i, v in enumerate(a): c[i] += v
    for i, v in enumerate(b): c[i] += v
    return c


def sub(a, b):
    c = a + [0] * max(0, len(b) - len(a))
    for i, v in enumerate(b): c[i] -= v
    assert all(v >= 0 for v in c)
    return c


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y: c[i+j] += x*y
    return c


def shift(a, k):
    return [0] * k + list(a)


def prod(args):
    p = [1]
    for x in args: p = mul(p, x)
    return p


def power(a, n):
    out = [1]
    while n:
        if n % 2: out = mul(out, a)
        n //= 2
        if n: a = mul(a, a)
    return out


def binomial_two(m):
    return [comb(m, i) << (m-i) for i in range(m+1)]


def state(ch, v):
    """A: included; B: absent/dominated; C: absent/undominated root."""
    child = [state(ch, w) for w in ch[v]]
    A = shift(prod([add(add(a, b), c) for a, b, c in child]), 1)
    C = prod([b for a, b, c in child])
    B = sub(prod([add(a, b) for a, b, c in child]), C)
    return A, B, C


def build_tree(ks, tail=0):
    ch = [[]]
    for k in ks:
        hub = len(ch); ch.append([]); ch[0].append(hub)
        for _ in range(k):
            a = len(ch); ch.append([]); ch[hub].append(a)
            b = len(ch); ch.append([]); ch[a].append(b)
            c = len(ch); ch.append([]); ch[b].append(c)
    last = 0
    for _ in range(tail):
        v = len(ch); ch.append([]); ch[last].append(v); last=v
    return ch


def poly_tree(ks, tail=0):
    ch = build_tree(ks, tail)
    A, B, C = state(ch, 0)
    return ch, A, B, add(A, B)


def gamma_and_failures(d):
    g = next(j for j, v in enumerate(d) if v)
    fail = [j for j in range(1, len(d)-1) if d[j]*d[j] < d[j-1]*d[j+1]]
    j = 0
    while j+1 < len(d) and d[j] <= d[j+1]: j+=1
    while j+1 < len(d) and d[j] >= d[j+1]: j+=1
    return g, fail, j == len(d)-1


def canonical(ch):
    n=len(ch); adj = [set(x) for x in ch]
    for v, children in enumerate(ch):
        for w in children: adj[w].add(v)
    leaves = [i for i in range(n) if len(adj[i]) <= 1]
    alive = [True] * n; rem=n
    while rem > 2:
        nxt=[]
        for v in leaves:
            alive[v]=False; rem-=1
            for w in adj[v]:
                adj[w].remove(v)
                if len(adj[w])==1: nxt.append(w)
            adj[v].clear()
        leaves=nxt
    centers=[v for v in range(n) if alive[v]]
    original=[set(x) for x in ch]
    for v, children in enumerate(ch):
        for w in children: original[w].add(v)
    def encode(v, parent):
        return '('+''.join(sorted(encode(w,v) for w in original[v] if w != parent))+')'
    return min(encode(c,-1) for c in centers)


def hub_states(k):
    """Construct an actual hub with k length-three paths and run state DP."""
    ch=build_tree([k]); hub=ch[0][0]
    return state(ch,hub)


def W_dp(ks, m):
    """Compute W by direct child-subtree states, grouping identical P_2 arms."""
    H=[hub_states(k) for k in ks]
    S=prod([add(add(a,b),c) for a,b,c in H])
    AB=prod([add(a,b) for a,b,c in H])
    BV=prod([b for a,b,c in H])
    # Each pendant P_2 has (S,AB,B)=(x(x+2),x(x+2),x).
    arms=shift(binomial_two(m),m)
    A=shift(mul(S, arms),1)
    B=sub(mul(AB,arms),shift(BV,m))
    return add(A,B)


def W_formula(ks, m):
    ff=[];gg=[];ww=[]
    for k in ks:
        f=add(shift(power(mul([1,1],[2,1]),k),1),power([1,3,1],k))
        g=sub(f,power([1,1],k))
        w=sub(power([1,3,1],k),power([1,1],k))
        ff.append(f);gg.append(g);ww.append(w)
    base=sub(mul(binomial_two(m),add(shift(prod(ff),1),prod(gg))),prod(ww))
    return shift(base,sum(ks)+m)


def jump(d,j):
    n=len(d)-1
    return Fraction(1) + Fraction((n-j+1)*d[j-1],d[j]) - Fraction((n-j)*d[j],d[j+1])


def above_two_jump_indices(d):
    g,_,_=gamma_and_failures(d); n=len(d)-1; out=[]
    for j in range(g+1,n):
        a = d[j]*d[j+1]+(n-j+1)*d[j-1]*d[j+1]-(n-j)*d[j]*d[j]
        if a > 2*d[j]*d[j+1]: out.append(j)
    return out


def audit():
    res={"P16_P18":{}, "P19":{}, "P22_P23":{}, "P27":{}, "failures":[]}
    expected_U=[0]*9+[2,75,2837,27278,132791,403364,842457,1277429,1454340,
                     1270263,862444,458002,190138,61213,15015,2718,343,27,1]
    for name, ks, tail, expect_gamma, expect_center, expect_without in [
        ('U',(2,2,3),2,9,[2,75,1141],[0,0,1696]),
        ('T(2,2,3)',(2,2,3),0,8,[1,37,552],[0,0,800]),
    ]:
        ch,A,B,d=poly_tree(ks,tail)
        g,fail,uni=gamma_and_failures(d)
        with_c=[A[g+i] for i in range(3)]
        without_c=[B[g+i] for i in range(3)]
        ok=(g==expect_gamma and with_c==expect_center and
            without_c==expect_without and uni and
            (d==expected_U if name=='U' else d[g:g+3]==[1,37,1352]))
        res['P16_P18'][name]={"n":len(ch), "gamma":g, "lc_fail":fail,
                              "unimodal":uni,"with_centre":with_c,
                              "without_centre":without_c,"match":ok}
        if not ok: res['failures'].append(name)

    observed=[]; duplicate={}; canon_seen={}; total_shapes=0
    for r in range(1,6):
        for ks in combinations_with_replacement(range(11),r):
            n=1+r+3*sum(ks)
            if n>34: continue
            ch,_,_,d=poly_tree(ks)
            if len(ch)!=n: raise AssertionError((ks,n,len(ch)))
            g,fail,uni=gamma_and_failures(d)
            key=canonical(ch); total_shapes+=1
            if key in canon_seen:
                duplicate[f'{r}:{ks}']=canon_seen[key]
            else: canon_seen[key]=f'{r}:{ks}'
            if not uni: res['failures'].append(f'nonunimodal T{ks}')
            if fail: observed.append({"ks":list(ks),"n":n,"gamma":g,"fail":fail,"unimodal":uni})
    expected=[(2,3,3),(2,3,4),(3,3,3),(2,3,5),(2,4,4),(3,3,4)]
    res['P19']={"nonLC":observed,"total_parameterizations":total_shapes,
                "distinct_shapes":len(canon_seen),"isomorphic_duplicates":duplicate,
                "match":sorted(tuple(o['ks']) for o in observed)==sorted(expected) and
                        all(o['fail']==[o['gamma']+1] and o['unimodal'] for o in observed)}
    if not res['P19']['match']:res['failures'].append('P19')

    # Independent exact formula vs explicit recursive three-state computation.
    small=0
    for k in range(1,5):
        for r in range(3,6):
            for m in range(1,7):
                ks=[k]*r
                x,y=W_dp(ks,m),W_formula(ks,m)
                if x!=y:res['failures'].append(f'W identity {ks},m={m}')
                small+=1
    res['P22_P23']['small_identity_checks']=small
    for tag,ks,m,lower in [('6501',[8,8,9],3211,2),('15485',[9,9,9],7700,Fraction(43,20))]:
        d1=W_dp(ks,m);d2=W_formula(ks,m)
        g,lc,uni=gamma_and_failures(d1)
        J=jump(d1,g+1)
        bad=above_two_jump_indices(d1)
        ok=d1==d2 and uni and J>lower and bad==[g+1]
        res['P22_P23'][tag]={"n":len(d1)-1,"gamma":g,"formula_DP_match":d1==d2,
                               "jump_at_gamma_plus_1":str(J),
                               "jump_approx":float(J),"above_threshold":J>lower,
                               "jump_above_two_indices":bad,"unimodal":uni,
                               "nonLC_count":len(lc),"pass":ok}
        if not ok:res['failures'].append('P23_'+tag)

    res['P27']={"K_h":{str(h):((h+1)**2+3)//4 for h in (3,4,5)},
                 "T_k_orders":{str(k):1+3+3*(3*k) for k in (1,2,3,4)},
                 "U_order":27}
    res['passed']=not res['failures'] and res['P19']['match']
    (HERE/'audit_numeric.json').write_text(json.dumps(res,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({"passed":res['passed'],"failures":res['failures'],
                      "P16_P18":res['P16_P18'],"P19":res['P19'],
                      "P22_P23":res['P22_P23'],"P27":res['P27']},ensure_ascii=False,indent=2))
    return 0 if res['passed'] else 1


if __name__=='__main__':
    raise SystemExit(audit())
