#!/usr/bin/env python3
"""Independent exact Euler product for the forest count in Remark 6.4."""
import json
from collections import Counter,defaultdict
from math import comb
from pathlib import Path

SRC=Path(__file__).resolve().parent
TREE=[json.loads(s) for s in (SRC/'third_27.jsonl').read_text().splitlines()
      if s.startswith('{')]

def counts(max_a,max_b,order_max=27):
    by_type=Counter()
    for row in TREE:
        if row['n']>order_max:continue
        for a,b,m in row['hist']:
            if a<=max_a and b<=max_b:
                by_type[(a,b)]+=m
    dp={(0,0):1}
    for (a,b),m in sorted(by_type.items()):
        nd=defaultdict(int)
        for (x,y),v in dp.items():
            k=0
            while x+k*a<=max_a and y+k*b<=max_b:
                nd[(x+k*a,y+k*b)]+=v*comb(m+k-1,k)
                k+=1
        dp=dict(nd)
    return dp

def n10_direct():
    # Distinct nonisomorphic free trees; enumerate forests as multisets of these.
    import sys
    sys.path.insert(0,str(SRC))
    from dp_semantics import rooted_codes,to_graph,canonical_unrooted
    codes=rooted_codes(10)
    types=[]
    for n in range(2,11):
        shapes=set(canonical_unrooted(to_graph(code)) for code in codes[n])
        types.extend((n,key,to_graph(key)) for key in shapes)
    entries=[]
    for n,code,adj in types:
        mask=[(1<<v) | sum(1<<w for w in adj[v]) for v in range(n)]
        gamma=n;Gamma=0
        for s in range(1<<n):
            if any(not s&nb for nb in mask):continue
            j=bin(s).count('1')
            gamma=min(gamma,j)
            minimal=all(any(not ((s & ~(1<<v))&nb) for nb in mask)
                        for v in range(n) if s>>v&1)
            if minimal:Gamma=max(Gamma,j)
        entries.append((n,n-gamma,Gamma-gamma))
    # direct unordered collection by individually enumerated tree shapes.
    out=Counter()
    def walk(start,n,a,b):
        out[(n,a,b)]+=1
        for i in range(start,len(entries)):
            size,aa,bb=entries[i]
            if n+size<=10:walk(i,n+size,a+aa,b+bb)
    walk(0,0,0,0)
    return out

def main():
    dp=counts(13,4,27)
    claimed=1290927
    answer=sum(v for (a,b),v in dp.items() if b==4)
    actual=n10_direct()
    # Euler product by n,a,b directly from all tree types on <=10.
    byclass=Counter()
    for row in TREE:
        n=row['n']
        if n>10:continue
        for a,b,m in row['hist']:byclass[(n,a,b)]+=m
    rhs={(0,0,0):1}
    for (n,a,b),m in sorted(byclass.items()):
        nxt=defaultdict(int)
        for (nn,aa,bb),v in rhs.items():
            k=0
            while nn+k*n<=10:
                nxt[(nn+k*n,aa+k*a,bb+k*b)]+=v*comb(m+k-1,k)
                k+=1
        rhs=dict(nxt)
    mismatch=[(k,actual.get(k,0),rhs.get(k,0)) for k in set(actual)|set(rhs)
              if actual.get(k,0)!=rhs.get(k,0)]
    result={'remark_value':answer,'claimed':claimed,
            'main_equal':answer==claimed,
            'direct_forests_n_le_10':sum(actual.values()),
            'euler_forests_n_le_10':sum(rhs.values()),
            'crosscheck_mismatch':len(mismatch),'examples':mismatch[:10]}
    (SRC/'REMARK_6_4.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    assert not mismatch and answer==claimed

if __name__=='__main__':main()
