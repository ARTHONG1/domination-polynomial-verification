#!/usr/bin/env python3
"""Exact algebraic and independent tree-DP checks from submitted equations.

Run: python3 identity_checks.py
Output: IDENTITY_CHECKS.json. Checks support, never replace, proofs.
"""
from __future__ import annotations

import itertools
import json
from fractions import Fraction
from math import comb
from pathlib import Path

HERE=Path(__file__).resolve().parent


def add(a,b):
    return [ (a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]


def sub(a,b):
    return [ (a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]


def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j]+=x*y
    return c


def power(a,n):
    v=[1]
    for _ in range(n):v=mul(v,a)
    return v


def norm(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:a.pop()
    return a


def coeff(a,i):
    return a[i] if 0<=i<len(a) else 0


def dp(adj):
    """Independent rooted-tree subset semantics via postorder, not submitted code."""
    n=len(adj)
    parent=[-1]*n
    order=[0]
    for v in order:
        for w in adj[v]:
            if w!=parent[v]:
                parent[w]=v
                order.append(w)
    assert len(order)==n
    states=[None]*n
    for v in reversed(order):
        A,B,C=[0,1],[0],[1]
        for w in adj[v]:
            if w==parent[v]:continue
            a,b,c=states[w]
            A,B,C=(mul(A,add(add(a,b),c)),
                   add(mul(B,add(a,b)),mul(C,a)),
                   mul(C,b))
        states[v]=(A,B,C)
    return norm(add(states[0][0],states[0][1]))


def W_graph(r,k,M):
    adj=[[]]
    def edge(a,b):
        adj[a].append(b);adj[b].append(a)
    def vertex(parent):
        new=len(adj);adj.append([]);edge(parent,new);return new
    for _ in range(r):
        hub=vertex(0)
        for __ in range(k):
            x=vertex(hub);y=vertex(x);vertex(y)
    for _ in range(M):
        x=vertex(0);vertex(x)
    return adj


def W_formula(r,k,M):
    x=[0,1];one=[1];xplus1=[1,1];xplus2=[2,1];quad=[1,3,1]
    f=add(mul(x,power(mul(xplus1,xplus2),k)), power(quad,k))
    g=sub(f,power(xplus1,k));w=sub(power(quad,k),power(xplus1,k))
    inside=sub(mul(power(xplus2,M),add(mul(x,power(f,r)),power(g,r))),power(w,r))
    return norm(([0]*(r*k+M))+inside)


def cb_identity(a,b,k):
    c=mul(a,b)
    lhs=coeff(c,k)**2-coeff(c,k-1)*coeff(c,k+1)
    rhs=0
    for i in range(-1,len(a)+2):
        for j in range(i+1,len(a)+2):
            rhs+=(coeff(a,i)*coeff(a,j-1)-coeff(a,i-1)*coeff(a,j))*(
                  coeff(b,k-j+1)*coeff(b,k-i)-coeff(b,k-j)*coeff(b,k-i+1))
    return lhs,rhs


def main():
    results={}
    # Cauchy–Binet 2×2 convolution identity: exact for arbitrary sequences;
    # enumerate independent signed, zero and positive boundary coefficients.
    checked=0
    cases=[tuple(x) for n in (1,2,3) for x in itertools.product((-1,0,1,2),repeat=n)]
    for a in cases:
        for b in cases:
            for k in range(len(a)+len(b)-1):
                l,r=cb_identity(a,b,k)
                assert l==r, (a,b,k,l,r)
                checked+=1
    results['cauchy_binet_exact_cases']=checked

    checked=0
    for h in range(0,12):
        K=((h+1)**2+3)//4
        for xnum in range(0,4*h+1):
            x=Fraction(xnum,2)
            if x>2*h:continue
            for J in (K,K+1,K+8):
                e=2*J-x
                assert 2*e-x*(2*h-x)==(x-(h+1))**2+4*J-(h+1)**2
                # e>0 follows separately from the graph incidence identity
                # and j>gamma; it does not follow from the range of x alone.
                assert x*(2*h-x)<=2*e
                checked+=1
    results['variance_jump_algebra_cases']=checked

    checked=0
    for n in range(5,201):
        for L in range(1,n):
            b=comb(n,2)-L
            u=comb(n,3)-L*(n-2)+comb(L,2)
            v=2*b*(b-1)-3*n*u
            assert 2*v==(n-1-L)*(L*(3*n-4)+n*(n-2))
            assert v>=0
            assert (v==0)==(L==n-1)
            checked+=1
    results['top_coefficient_factorization_cases']=checked

    variants=[]
    for r,k,M in [(3,1,1),(3,1,2),(3,2,1),(4,1,1),(5,1,1)]:
        g=W_graph(r,k,M)
        a,b=dp(g),W_formula(r,k,M)
        assert a==b,(r,k,M)
        variants.append({'r':r,'k':k,'M':M,'n':len(g),'coefficient_mismatch':0})
    results['W_formula_independent_tree_DP']=variants

    checked=0
    for r in (3,4,5):
        for k in range(1,13):
            f=add(mul([0,1],power([2,3,1],k)),power([1,3,1],k))
            fp=power(f,r)
            for i in range(1,r+1):
                assert coeff(fp,i) <= 2**(r+i)*(4*k)**i*2**(k*i)
                checked+=1
            for M in (r+1,2*r+6,2**(k+2)):
                for s in range(0,r):
                    if s==0:continue
                    base=comb(M,s)*2**(M-s)
                    surplus=sum(coeff(fp,i)*comb(M,s-i)*2**(M-s+i) for i in range(1,s+1))
                    theta=Fraction(surplus,base)
                    bound=2**r*sum(Fraction(16*k*s*2**k,M-s)**i for i in range(1,s+1))
                    assert 0<=theta<=bound
                    checked+=1
    results['W_coefficient_and_theta_bound_cases']=checked
    results['status']='pass'
    results['scope']='Exact algebraic finite checks and independent DP for chosen parameters; universal quantifier still requires proof'
    (HERE/'IDENTITY_CHECKS.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
    print('IDENTITY_CHECKS_OK',results)

if __name__=='__main__':main()
