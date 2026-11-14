#!/usr/bin/env python3
"""Definition-only check of D(G ⊔ H, x) = D(G, x) D(H, x) on random forests.

Fixed seed, full subset scan. Run: python3 component_product.py > COMPONENT_PRODUCT.json
"""
import json
import random
from collections import deque

R = random.Random(20261114)

def forest(n, edge_probability=0.4):
    parent=list(range(n))
    def find(x):
        while x != parent[x]: x=parent[x]
        return x
    edges=[]
    for a,b in R.sample([(a,b) for a in range(n) for b in range(a+1,n)],n*(n-1)//2):
        if R.random() > edge_probability: continue
        x,y=find(a),find(b)
        if x!=y:
            edges.append((a,b)); parent[x]=y
    return edges

def components(n,edges):
    adj=[set() for _ in range(n)]
    for a,b in edges:adj[a].add(b);adj[b].add(a)
    seen=set();parts=[]
    for v in range(n):
        if v in seen:continue
        part={v};todo=[v];seen.add(v)
        while todo:
            for w in adj[todo.pop()]:
                if w not in seen:seen.add(w);todo.append(w);part.add(w)
        parts.append(sorted(part))
    return parts

def dom_poly(n,edges):
    nb=[1<<v for v in range(n)]
    for a,b in edges:nb[a]|=1<<b;nb[b]|=1<<a
    out=[0]*(n+1)
    for s in range(1<<n):
        if all(s&c for c in nb):out[bin(s).count("1")]+=1
    return out

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def test(n,edges):
    direct=dom_poly(n,edges)
    computed=[1]
    for comp in components(n,edges):
        pos={v:i for i,v in enumerate(comp)}
        e=[(pos[a],pos[b]) for a,b in edges if a in pos and b in pos]
        computed=mul(computed,dom_poly(len(comp),e))
    return direct==computed

def main():
    pairs=0;multi=0;fail=[]
    for _ in range(600):
        a=R.randint(1,9);b=R.randint(1,10-a);n=a+b
        edges=forest(a,R.random())+[(x+a,y+a) for x,y in forest(b,R.random())]
        if not test(n,edges):fail.append({"n":n,"edges":edges})
        pairs+=1
    while multi<150:
        n=R.randint(3,10);edges=forest(n,0.22)
        if len(components(n,edges))<3:continue
        if not test(n,edges):fail.append({"n":n,"edges":edges})
        multi+=1
    if dom_poly(1,[])!=[0,1]:fail.append({"K1":True})
    out={"pairs_and_forests":pairs,"three_or_more_components":multi,
         "K1":[0,1],"violations":len(fail),"failures":fail[:10]}
    print(json.dumps(out,ensure_ascii=False))
    assert not fail

if __name__=="__main__":main()
