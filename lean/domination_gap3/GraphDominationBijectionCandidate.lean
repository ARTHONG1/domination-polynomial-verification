import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

namespace GapThreeGraphDominationAudit

/-- Closed-neighborhood domination on a vertex type α with adjacency relation adj. -/
def IsDominating {α : Type*} (adj : α → α → Prop) (S : Finset α) : Prop :=
  ∀ v : α, v ∈ S ∨ ∃ u ∈ S, adj v u

/-- 1. Closed-neighborhood domination is upward-closed under Finset inclusion. -/
theorem isDominating_upward {α : Type*} (adj : α → α → Prop)
    {S U : Finset α} (hSU : S ⊆ U) (hS : IsDominating adj S) :
    IsDominating adj U := by
  intro v
  rcases hS v with hvS | ⟨u, huS, hadj⟩
  · exact Or.inl (hSU hvS)
  · exact Or.inr ⟨u, hSU huS, hadj⟩

/-- 2. Complement of an inclusion-minimal dominating set is dominating in an isolate-free simple graph. -/
theorem isDominating_compl_of_minimal {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop)
    (h_loopless : ∀ v : α, ¬ adj v v)
    (h_symm : ∀ u v : α, adj u v → adj v u)
    (h_no_iso : ∀ v : α, ∃ w : α, adj v w)
    (M : Finset α)
    (hM_dom : IsDominating adj M)
    (hM_min : ∀ x ∈ M, ¬ IsDominating adj (M.erase x)) :
    IsDominating adj (Finset.univ \ M) := by
  intro x
  by_cases hxM : x ∈ M
  · by_contra h_not_dom
    push_neg at h_not_dom
    rcases h_not_dom with ⟨_, h_no_out⟩
    apply hM_min x hxM
    intro v
    by_cases hvx : v = x
    · subst hvx
      rcases h_no_iso v with ⟨w, hvw⟩
      have hwM : w ∈ M := by
        by_contra hw_not_M
        have hw_compl : w ∈ Finset.univ \ M :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw_not_M⟩
        exact h_no_out w hw_compl hvw
      have hwx : w ≠ v := by
        intro h_eq
        subst h_eq
        exact h_loopless w hvw
      exact Or.inr ⟨w, Finset.mem_erase.mpr ⟨hwx, hwM⟩, hvw⟩
    · by_cases hvM : v ∈ M
      · exact Or.inl (Finset.mem_erase.mpr ⟨hvx, hvM⟩)
      · rcases hM_dom v with hvM' | ⟨u, huM, huv⟩
        · exact False.elim (hvM hvM')
        · have hux : u ≠ x := by
            intro h_eq
            subst h_eq
            have hv_compl : v ∈ Finset.univ \ M :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvM⟩
            exact h_no_out v hv_compl (h_symm v u huv)
          exact Or.inr ⟨u, Finset.mem_erase.mpr ⟨hux, huM⟩, huv⟩
  · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxM⟩)

/-- 3. Exact round-trip bijection equations and uniform extension count. -/
theorem extension_deletion_bijection_and_degree {α : Type*} [Fintype α] [DecidableEq α]
    (S U : Finset α) (x : α) (hxS : x ∉ S) (hxU : x ∈ U) :
    (insert x S).erase x = S ∧
      insert x (U.erase x) = U ∧
      (Finset.univ \ S).card = Fintype.card α - S.card := by
  refine ⟨Finset.erase_insert hxS, Finset.insert_erase hxU, ?_⟩
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]

end GapThreeGraphDominationAudit
