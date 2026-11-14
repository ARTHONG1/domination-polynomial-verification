#!/usr/bin/env python3
"""Fresh independent census of manuscript Remark 6.8's T(k_1,...,k_r).

Input: explicit construction in fixed submitted main.tex lines 663-667.
Run: python3 family_remark_6_8.py
Output: FAMILY_REMARK_6_8.json. No submitted generator or DP imports.
"""
from __future__ import annotations
import itertools
import json
from collections import Counter
from pathlib import Path
from identity_checks import dp

HERE=Path(__file__).resolve().parent

def T(ks):
    adj=[[]]
    def vertex(v):
        u=len(adj);adj.append([]);adj[u].append(v);adj[v].append(u);return u
    for k in ks:
        hub=vertex(0)
        for _ in range(k):
            x=vertex(hub);y=vertex(x);vertex(y)
    return adj

def is_unimodal(a):
    j=0
    while j+1<len(a) and a[j]<=a[j+1]:j+=1
    return all(a[k]>=a[k+1] for k in range(j,len(a)-1))

def main():
    n_checked=0;by_order=Counter();fail=[];nonuni=[]
    for r in range(1,6):
        cap=(34-1-r)//3
        for ks in itertools.combinations_with_replacement(range(cap+1),r):
            n=1+r+3*sum(ks)
            if n>34:continue
            a=dp(T(ks))
            assert len(a)==n+1 and a[-1]==1
            gamma=next(j for j,v in enumerate(a) if v)
            lc=[j for j in range(1,n) if a[j]*a[j]<a[j-1]*a[j+1]]
            u=is_unimodal(a)
            n_checked+=1;by_order[str(n)]+=1
            if lc:
                fail.append({'k':list(ks),'r':r,'n':n,'gamma':gamma,
                             'logconcavity_failure_indices':lc,'unimodal':u})
                assert lc==[gamma+1] and u
    desired={(2,3,3),(2,3,4),(3,3,3),(2,3,5),(2,4,4),(3,3,4)}
    observed={tuple(f['k']) for f in fail}
    assert observed==desired,(observed,desired)
    assert len(fail)==6
    out={'parameters_checked':n_checked,'by_order':dict(sorted(by_order.items(),key=lambda t:int(t[0]))),
         'non_logconcave_families':fail,'expected_six_match':True,
         'all_six_unimodal':True,'all_six_only_gamma_plus_one':True,
         'status':'pass', 'scope':'r 1..5, sorted nonnegative k, 1+r+3Σk ≤34; independent rooted DP'}
    (HERE/'FAMILY_REMARK_6_8.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
    print('FAMILY_REMARK_6_8_OK',n_checked,'parameter choices; non-log-concave members:',[(z['k'],z['n']) for z in fail])

if __name__=='__main__':main()
