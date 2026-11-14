# Supplementary material

**Paper:** C. Hong, *Unimodality of domination polynomials of forests with upper
domination gap at most four*.

This archive contains everything needed to reproduce the computer-assisted
parts of the paper and to re-check the formalised statements.

## Contents

| Path | Purpose |
|---|---|
| computation/independent_check.cpp | Program I of Appendix A (Beyer–Hedetniemi rooted trees, centroid filter, sequential-merge recurrence, exhaustive subset check for small orders) |
| computation/wrom_check.cpp | Program II of Appendix A (WROM free-tree generator, product-form recurrence) |
| computation/bruteforce_tree.cpp | Enumerates all vertex subsets of one tree (Proposition 6.5) |
| computation/analyze.py | Recounts the 1 290 927 forests of Remark 6.4; checks the trees T_k of Beaton and Schoonhoven |
| computation/centre_split.py | The splitting according to the centre in Remark 6.7 |
| computation/families.py | The family T(k_1,...,k_r) of Remark 6.8 |
| computation/anneal_nonlc.cpp | Heuristic search mentioned in Section 7 |
| computation/jumps/verify_counterexample.py | Proposition 7.2: builds the trees with 6501 and 15485 vertices explicitly, computes their complete domination polynomials by the generic recurrence (validated against subset enumeration on 305 small trees) and tests c_{j+1} - c_j <= 2 exactly |
| computation/jumps/sharpness.py, family_low.py, search_small.py | Proposition 7.2(ii): formula (13) checked against the generic recurrence; rigorous lower bounds for the jump tending to 3, 5, 7; search for small examples |
| computation/jumps/restricted_census.cpp, restricted_on_family.py | Question 7.3: the range (n+2*gamma+1)/3 < j < n, for all trees with at most 26 vertices (Program II with an added test) and for members of the family |
| computation/jumps/check_boundary.py | Inequality c_{n-1} - c_{n-2} <= 1 - 2/n of Section 7: checked by subset enumeration on all 18247 labelled trees with 3 to 7 vertices and on 480 random trees with up to 100 vertices |
| computation/jumps/results/ | Outputs of these programs |
| computation/collect.py, cross_check.py | Collect raw outputs; compare the two programs order by order |
| computation/run_all.sh | Runs the whole computation |
| computation/results/ | Complete outputs of the runs reported in the paper |
| lean/ | Lean 4 sources of the statements listed in Appendix B, with CheckAxioms.lean and its output |
| third_party/NETWORKX-LICENSE.txt | Licence of NetworkX, from whose implementation the WROM successor routine in wrom_check.cpp was translated |
| SHA256SUMS | Checksums of all files |

## Reproducing the computation

Requirements: a C++17 compiler with 128-bit integers (clang or gcc) and Python 3.

    cd computation
    ./run_all.sh 22          # orders 2..22: about one minute; enough for Theorem 1.1
    ./run_all.sh 27 12       # orders 2..27 with 12 processes: about 3 CPU-hours

run_all.sh compiles the programs, runs both of them for every order, and calls
cross_check.py, which fails unless, for every order,

* Program I generated exactly r_n rooted trees and kept exactly t_n of them
  (r_n, t_n recomputed from the classical recurrences inside each program);
* Program II generated exactly t_n trees;
* both programs report the same number of non-log-concave trees (0 for
  n <= 26 and 1 for n = 27), no non-unimodal tree, and the same 64-bit
  fingerprint of the multiset of coefficient vectors;
* for orders up to 16, the exhaustive subset enumeration agrees with the
  recurrence and no dominating set violates 2*gamma-|S| <= a(S) <= 2*Gamma-|S|.

Each output line is a JSON object for one order (Program I splits the orders
23..27 into residue classes of the running index of the rooted tree; every
process still traverses and counts all rooted trees). The field "hist" is the
joint distribution of (n - gamma, Gamma - gamma) over the trees of that order,
and "max_mean_jump" is the largest value of c_{j+1} - c_j (Section 7).

The unique non-log-concave tree of order 27 is printed by Program I as a parent
array (results/program1_order_27_witness.txt); bruteforce_tree confirms its
domination polynomial by enumerating all 2^27 subsets:

    ./bruteforce_tree 0 1 2 3 1 5 6 1 8 9 0 11 12 13 11 15 16 0 18 19 20 18 22 23 0 25

## Environment of the reported runs

Apple M3 Pro, macOS 27.0.1, Apple clang 21.0.0 (-O3 -std=c++17), Python 3.9.6;
11 November 2026.

On 12 November 2026 the archive was unpacked into an empty directory and
./run_all.sh 27 10 was run unchanged. All checks passed, and
results/cross_check_report.json, the witness files and the outputs of
Program II were byte-identical to the files supplied here. The outputs of
Program I for orders 23 to 27 differ only in the split into residue classes
(10 processes instead of 12); their totals agree.

## Lean

Lean 4.27.0 with Mathlib at commit a3a10db0e9d66acbebf76c5e6a135066525ac900.

    cd lean
    lake exe cache get      # optional: download the Mathlib build cache
    lake build
    lake env lean CheckAxioms.lean

The stand-alone package given here (lakefile.toml and lake-manifest.json,
which pin Mathlib and its dependencies) was built from a fresh clone on
12 November 2026: lake build completed without errors, and
lake env lean CheckAxioms.lean reproduced CheckAxioms.output.txt. Every listed
theorem depends only on propext, Classical.choice and Quot.sound. The
correspondence between the Lean statements and the paper, and the parts of
the paper that are not formalised, are described in Appendix B.

