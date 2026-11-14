#!/usr/bin/env python3
"""Collects the raw outputs in logs/ into results/ (one file per program and order)."""
import glob, json, re, sys
from pathlib import Path
here = Path(__file__).resolve().parent
NL = chr(10)
MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 27
for n in range(23, MAX + 1):
    parts = sorted(glob.glob(str(here / 'logs' / ('extended_%d_part*.jsonl' % n))),
                   key=lambda f: int(re.search(r'part(\d+)', f).group(1)))
    lines = [open(f).read().strip() for f in parts]
    assert lines and all(lines), (n, 'missing or empty part')
    objs = [json.loads(l) for l in lines]
    assert sorted(o['res'] for o in objs) == list(range(objs[0]['mod'])), n
    (here / 'results' / ('program1_order_%02d.jsonl' % n)).write_text(NL.join(lines) + NL)
    print('program 1, order', n, 'parts', len(lines), 'trees', sum(o['free_generated'] for o in objs),
          'expected', objs[0]['free_expected'], 'non-log-concave', sum(o['logconcavity_failures'] for o in objs))
    f = here / 'logs' / ('wrom_%d.jsonl' % n)
    l = f.read_text().strip() if f.exists() else ''
    if l:
        (here / 'results' / ('program2_order_%02d.jsonl' % n)).write_text(l + NL)
        o = json.loads(l)
        print('program 2, order', n, 'trees', o['free_generated'], 'non-log-concave', o['logconcavity_failures'])
    else:
        print('program 2, order', n, 'NOT FINISHED')

