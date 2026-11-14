#!/usr/bin/env python3
"""Audit the submitted Program I's ≤16-vertex exhaustive subset records.

This checks previously generated records from the submitted code replay. It
does not rerun the 2^n subset search and does not certify source-code logic.
"""

from hashlib import sha256
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
EXPECTED_PDF = '4df950b679a7c906e53721b9fc551e482042dfa824a30aa5d6014f68dfa99c63'
# Public-repository layout: the submitted programs and their outputs are in
# computation/ at the repository root.
COMPUTATION = REPO / 'computation'


def main():
    pdf_sha = sha256((REPO / 'manuscript/manuscript_en.pdf').read_bytes()).hexdigest()
    assert pdf_sha == EXPECTED_PDF, 'Submitted PDF hash differs from frozen target'
    run_all = (COMPUTATION / 'run_all.sh').read_text()
    assert 'bin/independent_check "$n" "$n" 16' in run_all, 'BF=16 replay invocation absent'

    orders = []
    for n in range(2, 17):
        row1 = json.loads((COMPUTATION / f'results/program1_order_{n:02}.jsonl').read_text())
        row2 = json.loads((COMPUTATION / f'results/program2_order_{n:02}.jsonl').read_text())
        assert row1['n'] == row2['n'] == n
        assert row1['mod'] == 1 and row1['res'] == 0
        assert row1['rooted_generated'] == row1['rooted_expected']
        assert row1['free_generated'] == row1['free_expected'] == row2['free_generated'] == row2['free_expected']
        assert row1['bruteforce_trees'] == row1['free_generated']
        assert row1['bruteforce_mismatches'] == row1['critical_bound_violations'] == 0
        assert row1['logconcavity_failures'] == row2['logconcavity_failures'] == 0
        assert row1['unimodality_failures'] == row2['unimodality_failures'] == 0
        assert row1['support_failures'] == row1['mean_jump_violations'] == 0
        for k in ('coefficients', 'total_dominating_sets', 'max_coefficient', 'fingerprint', 'hist'):
            assert row1[k] == row2[k], (n, k)
        orders.append({'n': n, 'trees': row1['free_generated'],
                       'exhaustively_checked': row1['bruteforce_trees'],
                       'discrepancies': row1['bruteforce_mismatches'],
                       'critical_violations': row1['critical_bound_violations']})

    totals = {'trees': sum(x['trees'] for x in orders),
              'exhaustively_checked': sum(x['exhaustively_checked'] for x in orders)}
    assert totals == {'trees': 32507, 'exhaustively_checked': 32507}, totals
    assert orders[-1]['trees'] == orders[-1]['exhaustively_checked'] == 19320
    out = {
        'status': 'pass', 'submitted_pdf_sha256': EXPECTED_PDF,
        'replay_source': 'computation/results (outputs shipped with the submitted supplement)',
        'range': 'n=2..16 (the submitted runner excludes K1)',
        'orders': orders, 'totals': totals,
        'K1_excluded_from_32507': True,
        'n1_to16_if_K1_included': 32508,
        'scope_limit': ('Checks saved Program I/II replay records and their equality. '
                        'Independent C++ code review and full mathematical meaning audit remain separate.'),
    }
    (HERE / 'BF16_REPLAY_AUDIT.json').write_text(json.dumps(out, ensure_ascii=False, indent=2) + '\n')
    print('BF16_REPLAY_PASS orders=15 trees=32507 checked=32507 discrepancies=0 n16=19320')


if __name__ == '__main__':
    main()
