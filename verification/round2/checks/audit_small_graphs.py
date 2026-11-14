#!/usr/bin/env python3
"""Adversarial, definition-based finite graph audit for claims P1-P11,P21,P24.

Exhaust all *labelled* simple graphs on at most six vertices.  No tree DP,
closed formula, Lean theorem, or submission code is imported.  This is a
finite counterexample search, and deliberately makes no global proof claim.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def fail(pid, n, mask, detail):
    raise AssertionError(f'{pid}: n={n} graph-mask={mask} {detail}')


def per_graph(n, mask, counts):
    edges=list(combinations(range(n),2))
    adj=[0]*n
    parent=list(range(n)); cyc=False
    def find(a):
        while parent[a]!=a: a=parent[a]
        return a
    for bit,(u,v) in enumerate(edges):
        if mask>>bit & 1:
            adj[u]|=1<<v;adj[v]|=1<<u
            ru,rv=find(u),find(v)
            if ru==rv: cyc=True
            else: parent[ru]=rv
    forest=not cyc
    is_tree=forest and (n==0 or (n>=1 and len({find(v) for v in range(n)})==1))
    color=[-1]*n;bip=True
    for v in range(n):
        if color[v]>=0:continue
        color[v]=0; todo=[v]
        for a in todo:
            for b in range(n):
                if adj[a]>>b & 1:
                    if color[b]<0: color[b]=1-color[a];todo.append(b)
                    elif color[b]==color[a]: bip=False
    isolate=[v for v in range(n) if adj[v]==0]
    noiso=not isolate
    full=(1<<n)-1
    neighbors=[adj[v]|(1<<v) for v in range(n)]
    D=[False]*(1<<n)
    sizes=[0]*(1<<n)
    for s in range(1,1<<n):sizes[s]=sizes[s>>1]+(s&1)
    crit=[0]*(1<<n)
    d=[0]*(n+1); by_j=defaultdict(list)
    for s in range(1<<n):
        dominates=all(neighbors[v]&s for v in range(n))
        D[s]=dominates
        if dominates:d[sizes[s]]+=1;by_j[sizes[s]].append(s)
    gamma=next(i for i,ct in enumerate(d) if ct)
    Γ=0; minimal=[]
    for j,sets in by_j.items():
        for s in sets:
            critical=0
            for v in range(n):
                if s>>v&1 and not D[s&~(1<<v)]:critical+=1
            crit[s]=critical
            if critical==j:Γ=max(Γ,j);minimal.append(s)
    h=Γ-gamma
    alpha=0
    for s in range(1<<n):
        if all(not(adj[v]&s) for v in range(n) if s>>v&1):
            alpha=max(alpha,sizes[s])
    uni=any(all(d[j]<=d[j+1] for j in range(k)) and
            all(d[j]>=d[j+1] for j in range(k,n)) for k in range(n+1))

    # P1: positive support, critical monotonicity and incidence identity.
    if any((d[j]>0)!=(gamma<=j<=n) for j in range(n+1)):
        fail('P1.support',n,mask,d)
    for s in range(1<<n):
        if not D[s]:continue
        for t in range(1<<n):
            if not D[t] or s&t!=s:continue
            for v in range(n):
                if t>>v&1 and not D[t&~(1<<v)]:
                    if not(s>>v&1 and not D[s&~(1<<v)]):
                        fail('P1.critical',n,mask,(s,t,v))
    for j in range(1,n+1):
        if (n-j+1)*d[j-1] != sum(j-crit[s] for s in by_j[j]):
            fail('P1.incidence',n,mask,j)
    counts['P1']+=1

    # P2: Ore complement property.
    if noiso:
        for s in minimal:
            if not D[full^s]:fail('P2.Ore',n,mask,s)
        if n < gamma+Γ:fail('P2.bound',n,mask,(gamma,Γ))
        counts['P2']+=1

    # P3: remove isolated vertices; compare every dominating subset and rank.
    r=len(isolate)
    live=[v for v in range(n) if v not in isolate]
    nr=len(live)
    nd=[0]*(nr+1); nminimal=[]; minsz=[]
    new_neighbors=[sum((1<<k) for k,u in enumerate(live) if neighbors[v]>>u&1)
                   for v in live]
    for s in range(1<<nr):
        if not all(new_neighbors[k]&s for k in range(nr)):continue
        nd[bin(s).count('1')]+=1
        if all(not all(new_neighbors[k]&(s&~(1<<v)) for k in range(nr))
               for v in range(nr) if s>>v&1):
            nminimal.append(bin(s).count('1'))
    ngamma=next(i for i,v in enumerate(nd) if v)
    nΓ=max(nminimal)
    if d!=[0]*r+nd or gamma!=ngamma+r or Γ!=nΓ+r:
        fail('P3',n,mask,(d,nd,gamma,Γ))
    counts['P3']+=1

    if forest:
        for j,sets in by_j.items():
            for s in sets:
                if j+crit[s]<2*gamma:fail('P4',n,mask,(s,j,crit[s],gamma))
        counts['P4']+=1
    if bip:
        if Γ!=alpha:fail('P6',n,mask,(Γ,alpha))
        for j,sets in by_j.items():
            for s in sets:
                if j+crit[s]>2*alpha:fail('P5',n,mask,(s,j,crit[s],alpha))
        counts['P5_P6']+=1

    total=sum(d); avd=Fraction(sum(j*d[j] for j in range(n+1)),total)
    c={j:Fraction(sum(crit[s] for s in sets),len(sets)) for j,sets in by_j.items() if sets}
    var={j:sum(((Fraction(crit[s])-c[j])**2 for s in sets),Fraction(0))/len(sets)
         for j,sets in by_j.items() if sets}
    if forest:
        for j in range(1,n+1):
            if 3*j<=n+2*gamma+1 and d[j-1]>d[j]:fail('P7.increasing',n,mask,j)
        if 3*avd<n+2*gamma:fail('P7.avdLower',n,mask,(avd,gamma))
        counts['P7.forest']+=1
    if bip:
        for j in range(1,n+1):
            if 3*j>=n+2*alpha+1 and d[j-1]<d[j]:fail('P7.decreasing',n,mask,j)
        if 3*avd>n+2*alpha:fail('P7.avdUpper',n,mask,(avd,alpha))
        counts['P7.bipartite']+=1

    for j in range(gamma+1,n+1):
        if (j-c[j])*(c[j]-c[j-1])>var[j]:fail('P8.covariance',n,mask,j)
        if j<n and d[j-1]>=d[j]<d[j+1] and c[j+1]-c[j]<=2:
            fail('P8.valley',n,mask,j)
    counts['P8.general']+=1
    if forest:
        K=((h+1)**2+3)//4
        for j in range(gamma+K,n+1):
            if c[j]-c[j-1]>2:fail('P8.varianceJump',n,mask,j)
        if n-gamma>=3*K-7 and not uni:fail('P9',n,mask,(h,K))
        counts['P9']+=1
        if noiso:
            if not uni and (h<3 or n>6*K-h-16):fail('P10.ii',n,mask,(h,K))
            if 3*h*h+4*h-19<=2*n and not uni:fail('P10.iii',n,mask,(h,K))
            counts['P10']+=1
        if h<=3 and not uni:fail('P11',n,mask,h)
        counts['P11']+=1
        for j in range(gamma+1,n):
            if c[j+1]-c[j]>=2*(j-gamma)+1:
                fail('P21',n,mask,(j,c[j],c[j+1]))
        counts['P21']+=1
        if is_tree and n>=5:
            L=sum(1 for a in adj if bin(a).count('1')==1)
            b=comb(n,2)-L
            u=comb(n,3)-L*(n-2)+comb(L,2)
            if d[n-1]!=n or d[n-2]!=b or d[n-3]>u:
                fail('P24.counts',n,mask,(d,L,b,u))
            bound = c[n-1]-c[n-2]<=1-Fraction(2,n)
            equal = c[n-1]-c[n-2]==1-Fraction(2,n)
            if not bound or equal != (L==n-1):
                fail('P24.top',n,mask,(L,b, c[n-1]-c[n-2]))
            counts['P24']+=1


def main():
    counts=Counter()
    for n in range(7):
        for mask in range(1<<(n*(n-1)//2)):
            per_graph(n,mask,counts)
    out={"max_order":6,"labelled_graphs":sum(1<<(n*(n-1)//2) for n in range(7)),
         "checked":dict(counts),"passed":True}
    (HERE/'audit_small_graphs.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(out,ensure_ascii=False,indent=2))


if __name__=='__main__':main()
