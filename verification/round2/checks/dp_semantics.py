#!/usr/bin/env python3
"""Independent rooted-state definition census for every free tree n<=12.

The graph family comes from multisets of canonical rooted parenthesis codes,
then free-tree duplicates are removed by rerooting at their centres.
"""
import json
from pathlib import Path
from collections import deque
from functools import lru_cache

def add(a,b):
    c=[0]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    return c

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def prod(polys):
    p=[1]
    for a in polys:p=mul(p,a)
    return p

def sub(a,b):
    c=a+[0]*max(0,len(b)-len(a))
    for i,x in enumerate(b):c[i]-=x
    assert min(c)>=0
    return c

def normalized(p,n):
    return p[:n]+[0]*max(0,n-len(p))

def rooted_codes(max_n):
    by_n={1:['()']}
    for n in range(2,max_n+1):
        children=sorted((code,k) for k,values in by_n.items() for code in values)
        found=[]
        def choose(start,rem,items):
            if rem==0:
                found.append('('+''.join(items)+')');return
            for pos in range(start,len(children)):
                code,size=children[pos]
                if size<=rem:choose(pos,rem-size,items+[code])
        choose(0,n-1,[])
        by_n[n]=found
    return by_n

def to_graph(code):
    adj=[];stack=[]
    for c in code:
        if c=='(':
            v=len(adj);adj.append([])
            if stack:
                p=stack[-1];adj[v].append(p);adj[p].append(v)
            stack.append(v)
        else:
            stack.pop()
    return adj

def canonical_unrooted(adj):
    n=len(adj)
    if n==1:return '()'
    remaining=set(range(n))
    leaves=[v for v in range(n) if len(adj[v])<=1]
    while len(remaining)>2:
        for v in leaves:remaining.remove(v)
        leaves=[v for v in remaining if sum(w in remaining for w in adj[v])<=1]
    @lru_cache(None)
    def code(v,parent):
        return '('+''.join(sorted(code(w,v) for w in adj[v] if w!=parent))+')'
    return min(code(c,-1) for c in remaining)

def states(adj,root,checks):
    n=len(adj)
    parent=[-2]*n;parent[root]=-1;order=[root]
    for v in order:
        for w in adj[v]:
            if w!=parent[v]:
                parent[w]=v;order.append(w)
    children=[[] for _ in range(n)]
    for v in order[1:]:children[parent[v]].append(v)
    dp=[None]*n
    subtree=[0]*n
    nbh=[sum(1<<w for w in adj[v])|(1<<v) for v in range(n)]
    for v in reversed(order):
        c=children[v]
        subtree[v]=1<<v
        for w in c:subtree[v]|=subtree[w]
        A=[0,1]
        B=[0]
        C=[1]
        for w in c:
            a,b,d=dp[w]
            sw=add(add(a,b),d)
            A2=mul(A,sw)
            B2=add(mul(B,add(a,b)),mul(C,a))
            C2=mul(C,b)
            A,B,C=A2,B2,C2
        na=1+sum(subtree[v]>>u&1 for u in range(n) if u!=v)
        aa=[0]*(na+1);bb=[0]*(na+1);cc=[0]*(na+1)
        verts=[u for u in range(n) if subtree[v]>>u&1]
        bit=[1<<u for u in verts]
        # Independent definition: all descendants (except v) dominated internally.
        for q in range(1<<na):
            mask=0
            for i,b0 in enumerate(bit):
                if q>>i&1:mask|=b0
            if any((nbh[u]&mask)==0 for u in verts if u!=v):continue
            poly=aa if (mask>>v&1) else (bb if nbh[v]&mask else cc)
            poly[bin(q).count('1')]+=1
        got=tuple(normalized(z,na+1) for z in (A,B,C))
        want=(aa,bb,cc)
        checks['rooted_vertex_checks']+=1
        if got!=want:
            checks['violations'].append({'root':root,'v':v,'n':n,'got':got,'want':want})
        dp[v]=(A,B,C)
    rA,rB,_=dp[root]
    d=add(rA,rB)
    # True polynomial is counted by all subsets satisfying the domination definition.
    full=(1<<n)-1
    real=[0]*(n+1)
    for s in range(1<<n):
        if all((nbh[v]&s)!=0 for v in range(n)):
            real[bin(s).count('1')]+=1
    if normalized(d,n+1)!=real:
        checks['violations'].append({'root':root,'n':n,'root_DP_mismatch':True})
    checks['root_checks']+=1

def main():
    expected={1:1,2:1,3:1,4:2,5:3,6:6,7:11,8:23,9:47,10:106,11:235,12:551}
    rooted=rooted_codes(12)
    checks={'root_checks':0,'rooted_vertex_checks':0,'violations':[],
            'free_by_n':{},'rooted_by_n':{}}
    for n in range(1,13):
        unique={}
        for code in rooted[n]:
            adj=to_graph(code)
            key=canonical_unrooted(adj)
            unique[key]=adj
        checks['free_by_n'][str(n)]=len(unique)
        checks['rooted_by_n'][str(n)]=len(rooted[n])
        if len(unique)!=expected[n]:
            checks['violations'].append({'n':n,'count':len(unique),'expected':expected[n]})
        for adj in unique.values():
            for root in range(n):states(adj,root,checks)
        print('checked',n,len(unique),'violations',len(checks['violations']),flush=True)
    path=Path(__file__).resolve().parent/'DP_SEMANTICS.json'
    with open(path,'w') as f:json.dump(checks,f,indent=2)
    print('DP_SEMANTICS',checks['root_checks'],checks['rooted_vertex_checks'],
          len(checks['violations']),flush=True)
    assert not checks['violations']

if __name__=='__main__':main()
