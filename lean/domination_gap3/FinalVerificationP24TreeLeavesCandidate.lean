import Mathlib
import domination_gap3.FinalVerificationP24GraphBridgeCandidate

/-! Derive the two distinct closed-neighborhood hypotheses used in the P24
graph-level proof directly from connectedness and degree-one leaves. -/

namespace FinalVerificationP24TreeLeaves

open FinalVerificationP24GraphBridge GapThreeGraphConnectionAudit

theorem leaf_closed_nbr_card_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) (hdeg : G.degree v = 1) :
    (closedNbr G v).card = 2 := by
  classical
  obtain ⟨w, hvw, hunique⟩ := (G.degree_eq_one_iff_existsUnique_adj).mp hdeg
  have hne : v ≠ w := by
    intro heq
    subst w
    exact G.irrefl hvw
  have heq : closedNbr G v = {v, w} := by
    ext u
    simp only [closedNbr, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hu
      rcases hu with h | h
      · exact Or.inl h
      · exact Or.inr (hunique u h)
    · intro hu
      rcases hu with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hvw
  rw [heq]
  simp [hne]

theorem adjacent_degree_one_vertices_force_card_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (v w : α) (hvw : G.Adj v w)
    (hv : G.degree v = 1) (hw : G.degree w = 1) :
    Fintype.card α ≤ 2 := by
  classical
  obtain ⟨_, _, huniqueV⟩ := (G.degree_eq_one_iff_existsUnique_adj).mp hv
  obtain ⟨_, _, huniqueW⟩ := (G.degree_eq_one_iff_existsUnique_adj).mp hw
  have huniV : ∀ y : α, G.Adj v y → y = w := by
    intro y h
    exact (huniqueV y h).trans (huniqueV w hvw).symm
  have huniW : ∀ y : α, G.Adj w y → y = v := by
    intro y h
    exact (huniqueW y h).trans (huniqueW v (G.symm hvw)).symm
  have hclosed : ∀ x : α, (x = v ∨ x = w) →
      ∀ y : α, G.Adj x y → (y = v ∨ y = w) := by
    intro x hx y hxy
    rcases hx with rfl | rfl
    · exact Or.inr (huniV y hxy)
    · exact Or.inl (huniW y hxy)
  have hreach : ∀ u : α, Relation.ReflTransGen G.Adj v u → (u = v ∨ u = w) := by
    intro u hr
    induction hr with
    | refl => exact Or.inl rfl
    | tail hprev hadj ih => exact hclosed _ ih _ hadj
  have huniv : (Finset.univ : Finset α) ⊆ {v, w} := by
    intro u hu
    rcases hreach u ((G.reachable_iff_reflTransGen v u).mp (hconn v u)) with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
  have hcard : Fintype.card α ≤ ({v, w} : Finset α).card := by
    simpa using Finset.card_le_card huniv
  have hne : v ≠ w := by
    intro heq
    subst w
    exact G.irrefl hvw
  have hpair : ({v,w} : Finset α).card = 2 := by simp [hne]
  omega

theorem distinct_degree_one_closed_nbr
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 3 ≤ Fintype.card α)
    (v w : α) (hv : G.degree v = 1) (hw : G.degree w = 1)
    (hne : v ≠ w) :
    closedNbr G v ≠ closedNbr G w := by
  classical
  intro heq
  have hvN : v ∈ closedNbr G w := by
    rw [← heq]
    simp [closedNbr]
  have hvw : G.Adj w v := by
    simp only [closedNbr, Finset.mem_filter, Finset.mem_univ, true_and] at hvN
    rcases hvN with h | h
    · exact False.elim (hne h)
    · exact h
  have hb := adjacent_degree_one_vertices_force_card_two G hconn w v hvw hw hv
  omega

noncomputable def leafVertices {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  Finset.univ.filter (fun v => G.degree v = 1)

/-- The manuscript's full d_(n-3) bound now has real leaf vertices,
without an added assumption on the size/distinctness of their neighborhoods. -/
theorem connected_graph_top_three_count_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    [DecidablePred (IsDominating G.Adj)]
    (hconn : G.Connected) (hn : 5 ≤ Fintype.card α) :
    (domRank G.Adj (Fintype.card α - 3)).card +
      (leafVertices G).card * (Fintype.card α - 2) ≤
      (Fintype.card α).choose 3 + (leafVertices G).card.choose 2 := by
  classical
  have hleaf2 : ∀ v ∈ leafVertices G, (closedNbr G v).card = 2 := by
    intro v hv
    exact leaf_closed_nbr_card_two G v (Finset.mem_filter.mp hv).2
  have hdist : ∀ v ∈ leafVertices G, ∀ w ∈ leafVertices G,
      v ≠ w → closedNbr G v ≠ closedNbr G w := by
    intro v hv w hw hne
    exact distinct_degree_one_closed_nbr G hconn (by omega) v w
      (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2 hne
  exact dominating_top_three_bound G (leafVertices G) hleaf2 hdist (by omega)

end FinalVerificationP24TreeLeaves
