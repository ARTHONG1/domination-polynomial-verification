import Mathlib

namespace GapThreeCriticalConflictCount

def IsDominating {α : Type*} (adj : α → α → Prop) (S : Finset α) : Prop :=
  ∀ w : α, w ∈ S ∨ ∃ u ∈ S, adj w u

def critical {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (S : Finset α) : Finset α :=
  S.filter (fun x => ¬ IsDominating adj (S.erase x))

def conflictNeighbors {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (S : Finset α) (v : α) : Finset α :=
  S.filter (fun x => x ≠ v ∧ IsDominating adj (S.erase x) ∧
    ¬ IsDominating adj ((S.erase v).erase x))

theorem critical_card_after_erase {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (S : Finset α) (v : α)
    (hv : v ∈ S) (hdom_v : IsDominating adj (S.erase v)) :
    (critical adj (S.erase v)).card =
      (critical adj S).card + (conflictNeighbors adj S v).card := by
  have hcrit : critical adj (S.erase v) =
      critical adj S ∪ conflictNeighbors adj S v := by
    ext x
    simp only [critical, conflictNeighbors, Finset.mem_filter,
      Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hnev, hxS⟩, hbad⟩
      by_cases hrem : IsDominating adj (S.erase x)
      · exact Or.inr ⟨hxS, hnev, hrem, hbad⟩
      · exact Or.inl ⟨hxS, hrem⟩
    · intro h
      rcases h with ⟨hxS, hnold⟩ | ⟨hxS, hnev, hrem, hbad⟩
      · have hnev : x ≠ v := by
          intro heq
          subst x
          exact hnold hdom_v
        refine ⟨⟨hnev, hxS⟩, ?_⟩
        intro hdomBoth
        apply hnold
        intro w
        rcases hdomBoth w with hw | ⟨u, hu, hadj⟩
        · left
          simp only [Finset.mem_erase] at hw ⊢
          exact ⟨hw.1, hw.2.2⟩
        · right
          refine ⟨u, ?_, hadj⟩
          simp only [Finset.mem_erase] at hu ⊢
          exact ⟨hu.1, hu.2.2⟩
      · exact ⟨⟨hnev, hxS⟩, hbad⟩
  have hdisj : Disjoint (critical adj S) (conflictNeighbors adj S v) := by
    apply Finset.disjoint_left.mpr
    intro x hx hn
    have hnold : ¬IsDominating adj (S.erase x) :=
      (Finset.mem_filter.mp hx).2
    have hrem : IsDominating adj (S.erase x) :=
      (Finset.mem_filter.mp hn).2.2.1
    exact hnold hrem
  rw [hcrit, Finset.card_union_of_disjoint hdisj]

theorem lemma5_from_conflict_leaf {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (γ : ℕ)
    (hγ_min : ∀ S : Finset α, IsDominating adj S → γ ≤ S.card)
    (h_leaf : ∀ S : Finset α, IsDominating adj S →
      (∃ x ∈ S, IsDominating adj (S.erase x)) →
      ∃ v ∈ S, IsDominating adj (S.erase v) ∧
        (conflictNeighbors adj S v).card ≤ 1) :
    ∀ S : Finset α, IsDominating adj S →
      2 * γ ≤ (critical adj S).card + S.card := by
  have key : ∀ t : ℕ, ∀ S : Finset α, IsDominating adj S →
      S.card = γ + t → 2 * γ ≤ (critical adj S).card + S.card := by
    intro t
    induction t with
    | zero =>
      intro S hS hcard
      have hall : critical adj S = S := by
        simp only [critical]
        apply Finset.filter_true_of_mem
        intro x hx hdom
        have hpos := Finset.card_pos.mpr ⟨x, hx⟩
        have hmin := hγ_min (S.erase x) hdom
        rw [Finset.card_erase_of_mem hx] at hmin
        omega
      rw [hall]
      omega
    | succ t ih =>
      intro S hS hcard
      by_cases hsupp : ∃ x ∈ S, IsDominating adj (S.erase x)
      · obtain ⟨v, hv, hdom_v, hdeg⟩ := h_leaf S hS hsupp
        have hcardv := Finset.card_erase_of_mem hv
        have hrec := ih (S.erase v) hdom_v (by omega)
        have hcrit := critical_card_after_erase adj S v hv hdom_v
        omega
      · push_neg at hsupp
        have hall : critical adj S = S := by
          simp only [critical]
          exact Finset.filter_true_of_mem (fun x hx => hsupp x hx)
        rw [hall]
        have hmin := hγ_min S hS
        omega
  intro S hS
  have hmin := hγ_min S hS
  exact key (S.card - γ) S hS (by omega)

end GapThreeCriticalConflictCount
