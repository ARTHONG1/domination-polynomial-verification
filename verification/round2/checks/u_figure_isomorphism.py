#!/usr/bin/env python3
"""Canonical-form comparison: U as defined in the text, Figure 1 (TikZ source),
and the witnesses printed by the two programs. Run: python3 u_figure_isomorphism.py
"""
import json
import re
from pathlib import Path

from dp_semantics import canonical_unrooted

BASE=Path(__file__).resolve().parent
REPO=BASE.parents[2]
TEX=(REPO/'manuscript/submitted/main.tex').read_text()
FOLDER=REPO/'computation/results'

def text_tree():
    adj=[[]]
    def add(parent):
        v=len(adj);adj.append([parent]);adj[parent].append(v)
        return v
    for k in [2,2,3]:
        hub=add(0)
        for _ in range(k):
            a=add(hub);b=add(a);add(b)
    a=add(0);add(a)
    return adj

def fig_tree():
    block=TEX.split(r'\caption{The tree $U$ with $27$ vertices.}',1)[0].rsplit(r'\begin{tikzpicture}',1)[1]
    nodes=['r','h1','h2','h3','p1','p2']
    edges=[('r','h1'),('r','h2'),('r','h3'),('r','p1'),('p1','p2')]
    for label,loc in re.findall(r'\{h(\d)/([0-9,]+)\}',block):
        # Loop string is not what this regex matches, see dedicated extraction below.
        pass
    m=re.search(r'\{h1/([0-9]+),h1/([0-9]+),h2/([0-9]+),h2/([0-9]+),h3/([0-9]+),h3/([0-9]+),h3/([0-9]+)\}',block)
    assert m, 'Cannot parse Figure 1 arm assignments'
    for num,s in enumerate(m.groups()):
        hub=['h1','h1','h2','h2','h3','h3','h3'][num]
        a,b,c=['p'+s+'_'+str(t) for t in (1,2,3)]
        nodes += [a,b,c]
        edges += [(hub,a),(a,b),(b,c)]
    ix={s:i for i,s in enumerate(nodes)}
    adj=[[] for _ in nodes]
    for a,b in edges:
        adj[ix[a]].append(ix[b]);adj[ix[b]].append(ix[a])
    return adj

def witness(name):
    txt=(FOLDER/name).read_text()
    m=re.search(r'parents:\s*([\d\s]+?)\s*coefficients:',txt)
    assert m,(name,txt[:100])
    par=[int(s) for s in m.group(1).split()]
    adj=[[] for _ in range(len(par)+1)]
    for child,p in enumerate(par,1):
        adj[child].append(p);adj[p].append(child)
    return adj

def main():
    text_u=text_tree();fig_u=fig_tree()
    c=canonical_unrooted(text_u)
    files=['program1_order_27_witness.txt','program2_order_27_witness.txt']
    seen={'paper_text':canonical_unrooted(text_u),'figure1':canonical_unrooted(fig_u)}
    for f in files:seen[f]=canonical_unrooted(witness(f))
    result={'graph_order':len(text_u),
            'figure_order':len(fig_u),
            'all_isomorphic':len(set(seen.values()))==1,
            'codes_same_sha256':None,
            'witness_files':files,
            'string_code_length':len(c),
            'failures':[]}
    if not result['all_isomorphic']:result['failures'].append('non-isomorphic')
    if len(c)!=54:result['failures'].append('unexpected code length')
    import hashlib
    result['codes_same_sha256']=hashlib.sha256(c.encode()).hexdigest()
    (BASE/'U_FIGURE_ISOMORPHISM.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    assert not result['failures']

if __name__=='__main__':main()
