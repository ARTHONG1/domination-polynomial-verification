#!/usr/bin/env python3
"""Audit independent third tree census against both submitted programs.

Also recompute the gap-four forest boundary count directly from the
independent joint distribution using a truncated Euler product.
"""
from collections import defaultdict
import json
from math import comb
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = ROOT / "computation/results"
THIRD = HERE.parent / "third_27.jsonl"
OUT = HERE.parent / "third_crosscheck.json"


def third_rows():
    rows = {}
    for line in THIRD.read_text().splitlines():
        if line.startswith("{"):
            o = json.loads(line)
            rows[o["n"]] = o
    return rows


def prior(n, program):
    file = SOURCE / f"program{program}_order_{n:02d}.jsonl"
    lines = [json.loads(s) for s in file.read_text().splitlines() if s.strip()]
    assert sorted((z.get("res", 0) for z in lines)) == list(range(lines[0].get("mod", 1)))
    acc = defaultdict(int)
    hist = defaultdict(int)
    for obj in lines:
        for key in ("free_generated", "logconcavity_failures", "unimodality_failures"):
            acc[key] += obj[key]
        for q, h, ct in obj["hist"]:
            hist[(q, h)] += ct
    return dict(acc), dict(hist)


def forest_count(rows):
    """Product over tree isomorphism classes, excluding isolated vertices."""
    # A grouped tree type (n,q,h) occurs with multiplicity m.
    grouped = defaultdict(int)
    for n in range(2, 23):
        for q, h, m in rows[n]["hist"]:
            grouped[(n, q, h)] += m

    cap_n, cap_q, cap_h = 26, 13, 4
    dp = {(0, 0, 0): 1}
    for (n, q, h), multiplicity in sorted(grouped.items()):
        # Coefficients of (1 - x^n y^q z^h)^(-m).
        limit = min(cap_n // n, cap_q // q, cap_h // h if h else cap_n // n)
        coeffs = [comb(multiplicity + k - 1, k) for k in range(limit + 1)]
        result = defaultdict(int)
        for (old_n, old_q, old_h), ways in dp.items():
            for k, coeff in enumerate(coeffs):
                nn, nq, nh = old_n + k * n, old_q + k * q, old_h + k * h
                if nn <= cap_n and nq <= cap_q and nh <= cap_h:
                    result[(nn, nq, nh)] += ways * coeff
        dp = result
    per_order = {str(n): sum(ways for (nn, q, h), ways in dp.items()
                             if nn == n and h == 4)
                 for n in range(2, cap_n + 1)}
    return sum(per_order.values()), {key: value for key, value in per_order.items() if value}


def main():
    rows = third_rows()
    assert len(rows) == 26 and all(i in rows for i in range(2, 28)), "third run unfinished"
    summary = {"third_program": THIRD.name, "all_orders": [], "mismatches": [],
               "forest_boundary": None}
    for n in range(2, 28):
        this = rows[n]
        th = {(q, h): ct for q, h, ct in this["hist"]}
        assert sum(th.values()) == this["trees"]
        order_result = {"n": n, "trees": this["trees"],
                        "nonLC": this["nonLC"], "nonUnimodal": this["nonUnimodal"]}
        for program in (1, 2):
            prev, hist = prior(n, program)
            for field, test in (("free_generated", "trees"),
                                ("logconcavity_failures", "nonLC"),
                                ("unimodality_failures", "nonUnimodal")):
                if prev[field] != this[test]:
                    summary["mismatches"].append((n, program, field, prev[field], this[test]))
            if hist != th:
                diff = next(((key, hist.get(key), th.get(key))
                             for key in sorted(set(hist) | set(th)) if hist.get(key) != th.get(key)), None)
                summary["mismatches"].append((n, program, "hist", diff))
            order_result[f"program{program}_match"] = hist == th and all(
                prev[f] == this[t] for f, t in (("free_generated", "trees"),
                ("logconcavity_failures", "nonLC"), ("unimodality_failures", "nonUnimodal")))
        summary["all_orders"].append(order_result)

    total, per_order = forest_count(rows)
    expected = json.loads((SOURCE / "gap4_boundary_and_BS_trees.json").read_text())
    summary["forest_boundary"] = {"third_total": total,
                                   "third_by_order": per_order,
                                   "expected_total": expected["gap4_forests_with_n_minus_gamma_le_13"],
                                   "expected_by_order": expected["gap4_forests_by_order"],
                                   "match": total == expected["gap4_forests_with_n_minus_gamma_le_13"] and
                                   per_order == expected["gap4_forests_by_order"]}
    summary["passed"] = not summary["mismatches"] and summary["forest_boundary"]["match"]
    OUT.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"passed": summary["passed"], "mismatches": summary["mismatches"],
                      "forest_boundary": summary["forest_boundary"]}, ensure_ascii=False, indent=2))
    sys.exit(0 if summary["passed"] else 1)


if __name__ == "__main__":
    main()
