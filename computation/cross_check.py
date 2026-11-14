#!/usr/bin/env python3
"""Compares the outputs of Program I and Program II order by order.

Usage: python3 cross_check.py [MAX]      (default MAX = 27)
Reads results/program1_order_NN.jsonl and results/program2_order_NN.jsonl,
writes results/cross_check_report.json, and exits with an error unless every
check listed in README.md passes.
"""
import glob, json, sys
from pathlib import Path
here = Path(__file__).resolve().parent
MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 27
EXPECTED_NONLC = {27: 1}        # number of non-log-concave trees per order (0 if absent)
ADD = ["free_generated", "logconcavity_failures", "unimodality_failures", "support_failures",
       "bruteforce_trees", "bruteforce_mismatches", "critical_bound_violations", "coefficients",
       "total_dominating_sets", "mean_jump_violations"]

def load(prefix, n):
    f = here / "results" / ("%s_order_%02d.jsonl" % (prefix, n))
    return [json.loads(l) for l in f.read_text().splitlines() if l.strip()]

def merge(parts):
    o = dict(parts[0])
    assert all(p["rooted_generated"] == p["rooted_expected"] for p in parts), "rooted-tree count"
    if len(parts) > 1 or parts[0]["mod"] != 1:
        assert sorted(p["res"] for p in parts) == list(range(parts[0]["mod"])), "missing residue class"
        for k in ADD: o[k] = sum(p[k] for p in parts)
        o["max_coefficient"] = max(p["max_coefficient"] for p in parts)
        o["max_mean_jump"] = max(p["max_mean_jump"] for p in parts)
        o["fingerprint"] = "%016x" % (sum(int(p["fingerprint"], 16) for p in parts) % 2**64)
        h = {}
        for p in parts:
            for m, g, c in p["hist"]: h[(m, g)] = h.get((m, g), 0) + c
        o["hist"] = [[m, g, c] for (m, g), c in sorted(h.items())]
    return o

report = {"max_order": MAX, "orders": [], "all_ok": True}
for n in range(2, MAX + 1):
    a, (b,) = merge(load("program1", n)), load("program2", n)
    checks = {
        "program1_rooted_count": a["rooted_generated"] == a["rooted_expected"],
        "program1_tree_count": a["free_generated"] == a["free_expected"],
        "program2_tree_count": b["free_generated"] == b["free_expected"] == a["free_expected"],
        "nonlogconcave_as_expected": a["logconcavity_failures"] == b["logconcavity_failures"] == EXPECTED_NONLC.get(n, 0),
        "all_unimodal": a["unimodality_failures"] == b["unimodality_failures"] == 0,
        "support_is_interval": a["support_failures"] == 0,
        "bruteforce_agrees": a["bruteforce_mismatches"] == 0 and a["critical_bound_violations"] == 0,
        "mean_jump_at_most_two": a["mean_jump_violations"] == 0,
        "programs_agree": all(a[k] == b[k] for k in ("coefficients", "total_dominating_sets", "max_coefficient", "fingerprint", "hist")),
    }
    ok = all(checks.values())
    report["orders"].append({"n": n, "rooted_trees": a["rooted_generated"], "trees": a["free_generated"],
                             "nonlogconcave": a["logconcavity_failures"], "bruteforce_trees": a["bruteforce_trees"],
                             "fingerprint_program1": a["fingerprint"], "fingerprint_program2": b["fingerprint"],
                             "max_mean_jump": a["max_mean_jump"], "ok": ok,
                             "failed_checks": [k for k, v in checks.items() if not v]})
    report["all_ok"] &= ok
report["trees_examined_including_K1"] = 1 + sum(o["trees"] for o in report["orders"])
report["bruteforce_trees"] = sum(o["bruteforce_trees"] for o in report["orders"])
report["max_mean_jump"] = max(o["max_mean_jump"] for o in report["orders"])
(here / "results" / "cross_check_report.json").write_text(json.dumps(report, indent=1) + "\n")
print("orders 2..%d  trees examined (with K_1): %d  non-log-concave: %s  max mean jump: %.6f" % (
    MAX, report["trees_examined_including_K1"], {o["n"]: o["nonlogconcave"] for o in report["orders"] if o["nonlogconcave"]},
    report["max_mean_jump"]))
print("ALL CHECKS PASSED" if report["all_ok"] else "CHECKS FAILED: %s" % [(o["n"], o["failed_checks"]) for o in report["orders"] if not o["ok"]])
sys.exit(0 if report["all_ok"] else 1)

