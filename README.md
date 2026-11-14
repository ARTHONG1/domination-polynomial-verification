# Unimodality of domination polynomials of forests with upper domination gap at most four

[![Verification](https://github.com/ARTHONG1/domination-polynomial-verification/actions/workflows/verify.yml/badge.svg)](https://github.com/ARTHONG1/domination-polynomial-verification/actions/workflows/verify.yml)

한국어: [README.ko.md](README.ko.md)

Manuscript, programs, computational output, Lean 4 formalisation and verification record for

> Chanu Hong, *Unimodality of domination polynomials of forests with upper domination gap at most four*, 2026.

The paper has been submitted to a journal and is under review. After submission, every theorem, proof and computation in the manuscript was verified again; this repository is the complete record of that verification. **No error or counterexample was found.** Independent checks and counterexample reports are welcome ([Issues](https://github.com/ARTHONG1/domination-polynomial-verification/issues)).

## Results of the paper

For a finite simple graph G of order n let d_j(G) be the number of dominating sets of size j and D(G, x) = Σ d_j(G) x^j the domination polynomial. Let γ(G) be the domination number, Γ(G) the upper domination number, and h = Γ(G) − γ(G) the upper domination gap. Alikhani and Peng conjectured that D(G, x) is always unimodal; this is open even for trees.

1. **Theorem 1.1.** The domination polynomial of every forest F with Γ(F) − γ(F) ≤ 4 is unimodal.
2. **Theorem 1.2.** Let F be a forest of order n with gap h, and K_h = ⌈(h+1)²/4⌉. If n − γ(F) ≥ 3K_h − 7, then D(F, x) is unimodal. If F has no isolated vertices and D(F, x) is not unimodal, then h ≥ 3 and n ≤ 6K_h − h − 16.
3. **Theorem 1.3.** The domination polynomial of every tree with at most 26 vertices is log-concave, and exactly one of the 751,065,460 trees with 27 vertices is not.
4. **Proposition 7.2.** For every forest, c_{j+1} − c_j < 2(j − γ) + 1 for γ < j < n, where c_j is the mean number of critical vertices of the dominating sets of size j, and this bound is best possible for trees.

## Verification at a glance

| What was checked | Scale |
|---|---|
| Theorem statements checked by the Lean 4 kernel | 59, depending only on propext, Classical.choice and Quot.sound |
| Statements written separately from their proofs and matched by SafeVerify | 48 statements in 17 files |
| Trees enumerated exhaustively | 1,198,738,056 (all trees with at most 27 vertices), by three programs with different generators |
| Completeness of the enumeration | a canonical code computed for every generated tree of orders 2 to 27 (third program): all distinct, and the counts equal Otter's numbers |
| Complete reruns from the supplementary material alone | 2 runs of orders 2 to 27, with the same results as submitted |
| Direct enumeration of subsets, without the recurrence | all 32,507 trees of orders 2 to 16; all 2^27 subsets of the exceptional tree U |
| Sections 2 to 5 tested from the definitions | every labelled graph with at most 6 vertices (33,868); every labelled forest and bipartite graph with at most 7 vertices (79,594,429 assertions) |
| Inequality for the top coefficients (Section 7) | all 5,063,360 labelled trees with 3 to 9 vertices |
| Recurrence of Appendix A against the definition | 124,534 rooted subtrees, over every tree with at most 12 vertices and every root |
| Proofs re-derived sentence by sentence | all 20 proof environments and 3 further arguments |
| Numbers in the text | Table 1 (52 entries), the coefficients of U, constants and examples recomputed in exact arithmetic |

The Lean build and axiom audit, the exhaustive computation up to order 22, and the quick checks are run again by [GitHub Actions](https://github.com/ARTHONG1/domination-polynomial-verification/actions) on every commit. The heavier computations (orders 23 to 27, canonical codes up to order 27) take CPU-hours; their output and logs are in the repository.

## Evidence for each statement

"Lean" means that the statement is fixed in [verification/round2/lean_targets/](verification/round2/lean_targets/) (or in the submitted supplement) and that its proof in [lean/](lean/) is accepted by the Lean 4.27.0 kernel. "Computation" is exact integer or rational arithmetic. "Re-derivation" refers to the sentence-by-sentence notes in [verification/round2/notes/](verification/round2/notes/).

| Statement | Lean | Computation | Re-derivation |
|---|---|---|---|
| Lemma 2.1 (basic properties, incidence identity) | graph_domination_lemma3_identity | labelled graphs: [census](verification/round2/checks/SEC2_4_LABELLED_CENSUS.json), [definition checks](verification/round2/checks/DEFINITION_CHECKS.json) | [Sec. 2–5](verification/round2/notes/PROOF_REVIEW_SEC2_5.md) |
| Lemma 2.2 (Ore), n ≥ γ + Γ | OreAlpha | same | same |
| Lemma 2.3 (removing isolated vertices) | Isolates | same | same |
| Lemma 3.1 (forests: \|S\| + a(S) ≥ 2γ) | forest_critical_inequality | all subsets of 32,507 trees: [audit](verification/round2/checks/BF16_REPLAY_AUDIT.json) | same |
| Lemma 3.2 (bipartite: \|S\| + a(S) ≤ 2α), Γ = α | bipartite_critical_le_two_independence, OreAlpha | labelled bipartite graphs | same |
| Corollaries 3.3, 3.4 | left_wing_from_critical_lower | labelled forests and bipartite graphs | same, [hand proofs](verification/round2/notes/SEC2_4_HAND_PROOFS.md) |
| Lemmas 4.1–4.3 | MeanJumpNoStrict | same | same |
| Theorem 5.1 | GeneralHGraph | [definition checks](verification/round2/checks/DEFINITION_CHECKS.json) | same |
| Theorem 1.2 (i)–(iii) | GeneralGap, GapArithmetic | same | same |
| Corollary 5.2 (gap ≤ 3) | GapThreeFull | same | same |
| Lemma 6.2 (products of log-concave polynomials) | LogConcaveProduct | [identity checks](verification/round2/checks/IDENTITY_CHECKS.json) | [Sec. 6–7](verification/round2/notes/PROOF_REVIEW_SEC6_7_APPENDIX_A.md) |
| Theorem 6.1 (trees with ≤ 26 vertices) | computer-assisted | three programs: [comparison](verification/round2/checks/third_crosscheck.json); canonical codes: [log](verification/round2/checks/canonical_27.log); reruns | [completeness](verification/round2/notes/COMPLETENESS_PROOF.md) |
| Corollary 6.3 | LogConcaveProduct | [component product](verification/round2/checks/COMPONENT_PRODUCT.json) | same |
| Theorem 1.1 (gap ≤ 4) | GapThreeFull, GapFourBridge | the finite part n ≤ 22 is Theorem 6.1 | [proof chain](verification/round2/notes/THEOREM_1_1_CHAIN.md) |
| Remark 6.4 (1,290,927 forests) | | [recount](verification/round2/checks/REMARK_6_4.json) | |
| Proposition 6.5 (the tree U) | | [2^27 subsets](verification/round2/checks/U_BRUTEFORCE.json); [isomorphism with Figure 1](verification/round2/checks/U_FIGURE_ISOMORPHISM.json) | |
| Theorem 6.6 (uniqueness at order 27) | computer-assisted | three programs; canonical codes at order 27 | |
| Remarks 6.7, 6.8 | | [centre split](verification/round2/checks/U_BRUTEFORCE.json); [268 parameter choices](verification/round2/checks/FAMILY_REMARK_6_8.json) | |
| Section 7, numerical statements | | [exact maxima](verification/round2/checks/SEC7_JUMP_CENSUS.json) | |
| Proposition 7.2 (i) | JumpBound | | [Sec. 6–7](verification/round2/notes/PROOF_REVIEW_SEC6_7_APPENDIX_A.md) |
| Proposition 7.2 (ii), trees with 6,501 and 15,485 vertices | | [coefficient bounds](verification/round2/checks/PROP_7_2_EXACT.json); [full polynomials](verification/round2/checks/audit_numeric.json) | same, [second derivation](verification/round2/notes/P22_SECOND_PASS.md) |
| Inequality (top) and equality for stars | P24Final and six further files | [5,063,360 labelled trees](verification/round2/checks/P24_PRUFER_AUDIT.json) | [note](verification/round2/notes/P24_TOP_JUMP.md) |
| Appendix A (recurrence, programs, Table 1) | | [recurrence vs. definition](verification/round2/checks/DP_SEMANTICS.json); [Table 1](verification/round2/checks/TABLE_COUNTS.json) | [proof](verification/round2/notes/APPENDIX_A_DP_PROOF.md), [code audit](verification/round2/notes/APPENDIX_A_CODE_AUDIT.md) |
| Appendix B (scope of the formalisation) | rebuilt on each commit | | |

Theorem 1.1 for gap 4 and Theorem 1.3 are computer-assisted, as stated in the manuscript: they rest on the exhaustive computation of Appendix A. Everything else in the chain is a statement checked by the Lean kernel. The detailed table, in Korean, is in [verification/round2/README.md](verification/round2/README.md).

## Reproducing the checks

Requirements: a C++17 compiler with 128-bit integers (clang or gcc), Python 3.10 or later, and for the formal proofs Lean 4.27.0 (installed by elan from lean/lean-toolchain).

Orders 2 to 22, which is the range needed for Theorem 1.1, and the exceptional tree (about one minute):

    cd computation
    ./run_all.sh 22
    ./bin/bruteforce_tree 0 1 2 3 1 5 6 1 8 9 0 11 12 13 11 15 16 0 18 19 20 18 22 23 0 25

All quick checks of the second verification round (about two minutes), compared with the committed output:

    verification/round2/checks/run_quick_checks.sh

The complete range of Theorem 1.3, orders 2 to 27 (about 3 CPU-hours):

    cd computation
    ./run_all.sh 27 12

Lean build and axiom audit:

    cd lean
    lake exe cache get
    lake build
    lake env lean CheckAxioms.lean
    lake env lean RefereeAudit.lean
    lake env lean Round2CheckAxioms.lean

## Contents

| Path | Contents |
|---|---|
| [manuscript/](manuscript/) | the manuscript as submitted (PDF and LaTeX source) and a Korean translation |
| [computation/](computation/) | the two exhaustive programs, the subset enumerator, the scripts for Section 7, and their output |
| [lean/](lean/) | Lean 4 package: the formalisation of Appendix B and the proofs added during verification |
| [independent_checks/](independent_checks/) | a further tree generator and exact tests on disconnected forests and bipartite graphs with cycles |
| [verification/](verification/) | the verification record: rerun before submission, first round, second round |
| [docs/](docs/) | description of the supplementary material, notes on the tree U |
| [SHA256SUMS](SHA256SUMS) | SHA-256 of every file |

The submitted manuscript is [manuscript/manuscript_en.pdf](manuscript/manuscript_en.pdf), SHA-256 `4df950b679a7c906e53721b9fc551e482042dfa824a30aa5d6014f68dfa99c63`. The single LaTeX file as submitted is [manuscript/submitted/main.tex](manuscript/submitted/main.tex); line numbers in the verification notes refer to it.

## Notes on the text of the manuscript

The verification found no mathematical error. It did find the following points of wording, none of which affects a theorem.

1. Appendix A says that there are 32,507 trees of order at most 16. This is the number for orders 2 to 16, the range processed by the program; with K₁ it is 32,508.
2. Lemma 2.3 and Theorem 1.2 do not state the convention for the graph of order zero (D = 1, γ = Γ = 0). For a forest all of whose vertices are isolated, D = x^n and the conclusions hold trivially.
3. Appendix A says that all arithmetic is exact integer arithmetic. This holds for every check that decides a statement. The statistic max_mean_jump printed by the first program is computed in floating point; its exact value, 73094/70925, was recomputed with rational arithmetic and confirms the bound 1.04 of Section 7.
4. The description of the supplementary material does not mention that jumps/check_boundary.py needs Python 3.10 or later, and that the supplied output of the first program was produced with 6 processes for orders 23 to 26 and 12 for order 27.

## How the verification was done

The verification was carried out by the author with AI coding agents; large language models were also used in writing the paper, as declared in the manuscript. For that reason the record is built from material that can be checked without relying on anyone's judgement: statements accepted by the Lean kernel, and exact computations that anyone can run again. The proofs in the manuscript were in addition re-derived sentence by sentence.

## Contact and licence

Chanu Hong, Gyeongin National University of Education, skdl3965@gmail.com.

Programs, scripts, Lean sources and verification data are released under the BSD 3-Clause licence ([LICENSE](LICENSE)). The manuscript files under manuscript/ are © 2026 Chanu Hong and are provided for reading and verification; they are not covered by the open-source licence. To cite this repository see [CITATION.cff](CITATION.cff).
