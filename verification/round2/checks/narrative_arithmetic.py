#!/usr/bin/env python3
"""Independent exact arithmetic checks for scattered manuscript claims.

Finite and arithmetic claims only (constants K_h, bounds, small examples).
Run: python3 narrative_arithmetic.py   (after table_counts.py > TABLE_COUNTS.json)
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
import json
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
TEX = Path(__file__).resolve().parents[3] / 'manuscript/submitted/main.tex'
SOURCE = TEX.read_text().splitlines()
OUT = HERE / 'NARRATIVE_ARITHMETIC.json'


def K(h: int) -> int:
    return ((h + 1) ** 2 + 3) // 4


def check_c4() -> tuple[int, int]:
    adj = [{1, 3}, {0, 2}, {1, 3}, {0, 2}]
    vertices = frozenset(range(4))

    def dominates(s: frozenset[int]) -> bool:
        covered = set(s)
        for v in s:
            covered.update(adj[v])
        return covered == vertices

    all_dom = [frozenset(s) for j in range(5) for s in combinations(range(4), j) if dominates(frozenset(s))]
    gamma = min(map(len, all_dom))
    triples = [s for s in all_dom if len(s) == 3]
    assert len(triples) == 4
    assert all(sum(not dominates(s - {v}) for v in s) == 0 for s in triples)
    assert gamma == 2
    return gamma, len(triples)


def main() -> None:
    checks: list[dict] = []

    def record(label: str, lines: list[int], value: object, justification: str) -> None:
        checks.append({
            'claim': label, 'main_tex_lines': lines,
            'source': {str(i): SOURCE[i - 1].strip() for i in lines},
            'result': value, 'justification': justification, 'status': 'checked',
        })

    assert [K(h) for h in range(6)] == [1, 1, 3, 4, 7, 9]
    assert {h: 6 * K(h) - h - 16 for h in (3, 4, 5)} == {3: 5, 4: 22, 5: 33}
    record('K_h and (ii) bound for h=3,4,5', [109, 120, 121],
           {'K0..5': [K(h) for h in range(6)], 'n_bound_3_4_5': [5, 22, 33]},
           'ceil via (q+3)//4, then 6K_h-h-16')

    assert 6*K(4) - 4 - 16 == 22 and 3*K(4) - 8 == 13
    record('gap-four finite bounds', [124, 644, 645, 646],
           {'n_upper': 22, 'n_minus_gamma_upper': 13}, 'exact integer arithmetic')

    assert all(2*(6*K(h)-h-16) <= 3*h*h + 4*h - 20 for h in range(10001))
    # Since 4*K(h) <= (h+1)^2+3, the inequality holds for EVERY integer h >= 0.
    record('bound using K_h <= ((h+1)^2+3)/4', [551, 552],
           {'checked_h': '0..10000', 'symbolic': '4K <= (h+1)^2+3 implies 2(6K-h-16) <= 3h^2+4h-20'},
           'ceil inequality from integer division; algebraic implication')

    assert all(3*h*h + 4*h - 19 <= 3*(h+1)**2 for h in range(10001))
    record('sqrt sufficient condition for (iii)', [119, 120],
           '3h²+4h−19 = 3(h+1)²−(2h+22) <= 2n if (h+1)²<=2n/3',
           'h>=0 makes 2h+22 positive')

    assert 3*K(5) - 7 == 20 and 3*K(5) - 8 == 19
    record('gap five n-gamma <=19', [751, 752],
           {'K5': K(5), 'nonunimodal_n_minus_gamma_max': 19},
           'contrapositive of Theorem 1.2(i), arithmetic portion only')

    assert (9*4+4) == 40 and all(9*k+4 >= 40 for k in range(4, 100))
    record('T_k order 9k+4 from k>=4', [141, 142], {'first_order': 40},
           'substitute k=4 and monotonicity in k')

    assert 1 + 3 + 3*(2+2+3) == 25 and 25+2 == 27
    record('T(2,2,3), U vertex counts', [665, 666, 670], {'base': 25, 'U': 27},
           '1+r+3sum(k_i), then append a path of 2 vertices')

    assert 1 + 3 + 3 * (8+8+9) + 2*3211 == 6501
    assert 1 + 3 + 3 * 3 * 9 + 2*7700 == 15485
    assert 1 + 3*9 + 7700 == 7728
    record('two giant tree orders and second gamma formula', [866, 867, 868, 869, 870],
           {'T889_M3211': 6501, 'W_r3_k9_M7700': 15485, 'gamma_W': 7728},
           'n=1+r+3sum(k_i)+2M, gamma=1+rk+M; gamma equality depends on P22 proof')

    g, triples = check_c4()
    assert 2 * g - 3 == 1
    record('C4 critical-vertex counterexample to forest lower bound', [332, 333, 334],
           {'gamma': g, 'triple_count': triples, 'a_of_each_triple': 0, '2gamma_minus_3': 1},
           'independent exhaustive subset and neighbor enumeration')

    poly = [0,1,4,6,5,1]
    assert poly == [0] + [comb(4,k-1) + (1 if k==4 else 0) for k in range(1,6)]
    assert poly == sorted(poly[:4]) + [poly[4],poly[5]]  # increasing then decreasing
    record('K1,4 domination polynomial', [568, 569, 570], poly,
           'sets containing centre: x(1+x)^4; only extra dominating set: four leaves')

    assert all(Fraction(n+2*G,3) <= Fraction(n+G,2) for n in range(1,101) for G in range(n+1))
    record('avd threshold comparison', [420, 421, 422],
           '(n+2Γ)/3 <= (n+Γ)/2 iff Γ<=n',
           'cross-multiply by 6; every independent set has at most n vertices')

    from_table = json.loads((HERE/'TABLE_COUNTS.json').read_text())
    record('table totals source cross-check', [133, 650, 1002, 1003],
           {'table_audit': from_table},
           'the output of table_counts.py is cited here, not recomputed in this script')

    out = {'source_sha256': __import__('hashlib').sha256(TEX.read_bytes()).hexdigest(),
           'checks': checks, 'verified_claim_groups': len(checks),
           'scope': 'arithmetic and finite claims'}
    OUT.write_text(json.dumps(out, ensure_ascii=False, indent=2) + '\n')
    print('NARRATIVE_ARITHMETIC_OK', len(checks), 'claim groups; no failed assertions')


if __name__ == '__main__':
    main()
