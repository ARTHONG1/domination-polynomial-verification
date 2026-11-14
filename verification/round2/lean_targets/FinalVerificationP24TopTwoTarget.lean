import Mathlib
import domination_gap3.FinalVerificationP24TreeLeavesCandidate

/-! Fixed P24 coefficient target. Zero oracle or extra assumption on
the actual graph leaves. Candidate must prove every named statement. -/

namespace FinalVerificationP24TopTwo

open FinalVerificationP24TreeLeaves
open FinalVerificationP24GraphBridge
open GapThreeGraphConnectionAudit

noncomputable def forbiddenPairs {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) : Finset (Finset α) := by
  classical
  exact (Finset.univ.powersetCard 2).filter
    (fun U => ¬ IsDominating G.Adj (Finset.univ \ U))

theorem nondom_iff_has_closed_nbr
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (D : Finset α) :
    (¬ IsDominating G.Adj D) ↔
      ∃ v : α, closedNbr G v ⊆ (Finset.univ \ D) := by
  sorry

theorem two_compl_bad_is_leaf_nbr
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 3 ≤ Fintype.card α)
    (U : Finset α) (hUcard : U.card = 2)
    (hbad : ¬ IsDominating G.Adj (Finset.univ \ U)) :
    ∃ v ∈ leafVertices G, closedNbr G v = U := by
  sorry

theorem forbidden_pairs_eq_leaf_nbr_image
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 3 ≤ Fintype.card α) :
    forbiddenPairs G = (leafVertices G).image (closedNbr G) := by
  sorry

theorem forbidden_pairs_count_eq_leaves
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 3 ≤ Fintype.card α) :
    (forbiddenPairs G).card = (leafVertices G).card := by
  sorry

theorem penultimate_domination_coefficient_exact
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    [DecidablePred (IsDominating G.Adj)]
    (hconn : G.Connected) (hn : 5 ≤ Fintype.card α) :
    (domRank G.Adj (Fintype.card α - 2)).card +
      (leafVertices G).card = (Fintype.card α).choose 2 := by
  sorry

end FinalVerificationP24TopTwo
