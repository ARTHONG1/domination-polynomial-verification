import Mathlib
import domination_gap3.FinalVerificationP24OverlapCandidate
import domination_gap3.GraphConnectionTheoremCandidate

/-! Graph-level bridge between actual dominating-set counts and the
P24 three-subset Bonferroni bound.  Leaf-pair distinctness remains to be
derived from tree connectivity/acyclicity in the final P24 theorem. -/

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
  classical
  intro hsubset
  rcases hdom v with hv | ⟨w, hw, hadj⟩
  · have hvN : v ∈ closedNbr G v := by simp [closedNbr]
    have hvComp := hsubset hvN
    exact (Finset.mem_sdiff.mp hvComp).2 hv
  · have hwN : w ∈ closedNbr G v := by simp [closedNbr, hadj]
    have hwComp := hsubset hwN
    exact (Finset.mem_sdiff.mp hwComp).2 hw

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
  classical
  let n := Fintype.card α
  let R := domRank G.Adj (n - 3)
  let T := (Finset.univ.powersetCard 3 : Finset (Finset α)) \
    (L.biUnion (fun v => tripleSupersets (closedNbr G v)))
  have hgood : R.image (fun D => Finset.univ \ D) ⊆ T := by
    intro U hU
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hU
    have hprops : D.card = n - 3 ∧ IsDominating G.Adj D :=
      (Finset.mem_filter.mp hD).2
    have hcard : (Finset.univ \ D).card = 3 := by
      have hpart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
      simp only [Finset.card_univ] at hpart
      omega
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    · intro hbad
      obtain ⟨v, hv, hN⟩ := Finset.mem_biUnion.mp hbad
      exact dominating_compl_excludes_closed_nbr G D hprops.2 v
        (Finset.mem_filter.mp hN).2
  have hinj : Set.InjOn (fun D : Finset α => Finset.univ \ D) (↑R) := by
    intro D hD E hE hEq
    have h := congrArg (fun U : Finset α => Finset.univ \ U) hEq
    simpa using h
  have hcimage := Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card hgood
  have habstract := allowed_triples_bound L (fun v => closedNbr G v) hleaf2 hdistinct
  change R.card + L.card * (n - 2) ≤ n.choose 3 + L.card.choose 2
  change T.card + L.card * (n - 2) ≤ n.choose 3 + L.card.choose 2 at habstract
  omega

end FinalVerificationP24GraphBridge
