#!/usr/bin/env python3
"""Recompute the rooted/free tree numbers of Table 1 and compare with the source.

Run: python3 table_counts.py > TABLE_COUNTS.json
"""
import json
import re
from pathlib import Path
SRC=Path(__file__).resolve().parents[3]/'manuscript/submitted/main.tex'
txt=SRC.read_text()
block=txt.split(r'\label{tab:counts}',1)[1].split(r'\end{tabular}',1)[0]
rows={}
for line in block.splitlines():
    m=re.match(r'\s*(\d+)\s*&\s*([\d\\,]+)\s*&\s*([\d\\,]+)\s*&\s*(\d+)\s*&\s*([\d\\,]+)\s*&\s*([\d\\,]+)',line)
    if m:
        for n,r,t in [(m[1],m[2],m[3]),(m[4],m[5],m[6])]:
            rows[int(n)]=(int(re.sub(r'[^0-9]','',r)),int(re.sub(r'[^0-9]','',t)))
root=[0]*28;tree=[0]*28;root[1]=1
for n in range(2,28):
    numerator=sum(sum(d*root[d] for d in range(1,j+1) if j%d==0)*root[n-j] for j in range(1,n))
    assert numerator%(n-1)==0
    root[n]=numerator//(n-1)
for n in range(1,28):
    correction=sum(root[k]*root[n-k] for k in range(1,n))
    if n%2==0:correction-=root[n//2]
    assert correction%2==0
    tree[n]=root[n]-correction//2
fail=[{"n":n,"reported":rows.get(n),"calculated":[root[n],tree[n]]}
      for n in range(2,28) if rows.get(n)!=(root[n],tree[n])]
sums={str(n):sum(tree[1:n+1]) for n in (16,22,26,27)}
expected={"22":9114285,"26":447672596,"27":1198738056}
for n,v in expected.items():
    if sums[n]!=v:fail.append({"sum_at":n,"got":sums[n],"want":v})
if len(rows)!=26:fail.append({"table_rows":len(rows)})
out={"table_rows":len(rows),"numbers":len(rows)*2,"errors":len(fail),
     "total":sums,"t27":tree[27],"r27":root[27],"failures":fail}
print(json.dumps(out,ensure_ascii=False,indent=2))
assert not fail

