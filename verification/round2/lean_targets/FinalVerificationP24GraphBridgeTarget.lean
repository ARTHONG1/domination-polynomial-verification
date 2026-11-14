import Mathlib
import domination_gap3.FinalVerificationP24OverlapCandidate
import domination_gap3.GraphConnectionTheoremCandidate

/-! Fixed graph/leaf-neighborhood interface for the submitted Section 7 P24.
This stage assumes the graph's selected leaf neighborhoods are distinct
2-sets. The separate tree-theoretic proof of those properties is still due. -/

namespace FinalVerificationP24GraphBridge

open FinalVerificationP24Overlap GapThreeGraphConnectionAudit

noncomputable def closedNbr {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (v : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun u => u = v ∨ G.Adj v u)

theorem dominating_compl_excludes_closed_nbr
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (D : Finset α)
    (hdom : IsDominating G.Adj D) (v : α) :
    ¬ closedNbr G v ⊆ (Finset.univ \ D) := by
  sorry

theorem dominating_top_three_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (L : Finset α)
    (hleaf2 : ∀ v ∈ L, (closedNbr G v).card = 2)
    (hdistinct : ∀ v ∈ L, ∀ w ∈ L, v ≠ w → closedNbr G v ≠ closedNbr G w)
    (hn : 3 ≤ Fintype.card α) :
    (domRank G.Adj (Fintype.card α - 3)).card +
      L.card * (Fintype.card α - 2) ≤
      (Fintype.card α).choose 3 + L.card.choose 2 := by
  sorry

end FinalVerificationP24GraphBridge
