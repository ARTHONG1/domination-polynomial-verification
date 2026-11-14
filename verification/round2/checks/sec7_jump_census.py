#!/usr/bin/env python3
"""Exact rational comparison of all previously enumerated n<=27 maxima.

Does not regenerate trees; input is third_jump_27.jsonl (third generator).
Run: python3 sec7_jump_census.py
"""
import json
from fractions import Fraction
from pathlib import Path
ROOT=Path(__file__).resolve().parent
COMP=ROOT.parents[2]/'computation'
rows=[json.loads(line) for line in (ROOT/'third_jump_27.jsonl').read_text().splitlines()
      if line.startswith('{')]
assert [z['n'] for z in rows]==list(range(2,28))
J=[(z['n'],Fraction(z['maxJump'][0],z['maxJump'][1]),z['maxJump'][2])
   for z in rows if z['maxJump'][2]!=-1]
R=[(z['n'],Fraction(z['maxRestricted'][0],z['maxRestricted'][1]),z['maxRestricted'][2])
   for z in rows if z['maxRestricted'][2]!=-1]
best=max(J,key=lambda p:p[1])
restricted=max([p for p in R if p[0]<=26],key=lambda p:p[1])
heur=[json.loads(line) for line in
      (COMP/'results/heuristic_mean_jump_search.jsonl').read_text().splitlines()
      if line.strip()]
heur_n=sorted(set(z['n'] for z in heur))
obj=max(-float(z['best_objective']) for z in heur)
ref=[line for line in (COMP/'jumps/results/restricted_census_orders_3_26.txt').read_text().splitlines() if line.startswith('RESTRICTED')]
fail=[]
if best[1]>=Fraction(26,25):fail.append('max_jump_not_below_1.04')
if restricted[1]>=1:fail.append('restricted_not_below_1')
if not all('restricted_jump_violations=0' in s for s in ref):fail.append('submitted_restricted_violation')
if heur_n!=[34,40,46,52,58]:fail.append({'unexpected_heuristic_orders':heur_n})
if obj>1.31:fail.append({'heuristic_max':obj})
out={'orders':[2,27],'total_trees':1+sum(z['trees'] for z in rows),
     'max_jump_exact':[best[0],str(best[1]),best[2]],'max_jump_float':float(best[1]),
     'restricted_up_to_26_exact':[restricted[0],str(restricted[1]),restricted[2]],
     'restricted_up_to_26_float':float(restricted[1]),
     'heuristic_orders':heur_n,'heuristic_reports':len(heur),
     'heuristic_max':obj,'restricted_census_rows':len(ref),'violations':fail}
with (ROOT/'SEC7_JUMP_CENSUS.json').open('w') as f:json.dump(out,f,indent=2)
print(json.dumps(out,indent=2))
assert not fail

if __name__=='__main__':pass
