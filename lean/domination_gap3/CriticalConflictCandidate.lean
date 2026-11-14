import Mathlib

namespace GapThreeCriticalConflict

def IsDominating {α : Type*} (adj : α → α → Prop) (S : Finset α) : Prop :=
  ∀ w : α, w ∈ S ∨ ∃ u ∈ S, adj w u

def footprint {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidableRel adj]
    (S : Finset α) (w : α) : Finset α :=
  S.filter (fun u => w = u ∨ adj w u)

theorem two_removals_witness {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidableRel adj]
    (S : Finset α) (x v : α)
    (hx : x ∈ S) (hv : v ∈ S) (hneq : x ≠ v)
    (hdom_x : IsDominating adj (S.erase x))
    (hdom_v : IsDominating adj (S.erase v)) :
    (¬ IsDominating adj ((S.erase v).erase x)) ↔
      ∃ w, footprint adj S w = ({x, v} : Finset α) := by
  classical
  constructor
  · intro hbad
    obtain ⟨w, hbadw⟩ : ∃ w, ¬(w ∈ (S.erase v).erase x ∨
        ∃ u ∈ (S.erase v).erase x, adj w u) := by
      simpa only [IsDominating, not_forall] using hbad
    have no_other_cover (u : α) (hu : u ∈ S) (hux : u ≠ x) (huv : u ≠ v) :
        ¬(w = u ∨ adj w u) := by
      intro hc
      have huEr : u ∈ (S.erase v).erase x := by
        simp only [Finset.mem_erase]
        exact ⟨hux, huv, hu⟩
      apply hbadw
      rcases hc with hwu | hadj
      · left
        simpa [hwu] using huEr
      · right
        exact ⟨u, huEr, hadj⟩
    have hxcov : w = x ∨ adj w x := by
      rcases hdom_v w with hw | ⟨u, hu, hadj⟩
      · left
        by_contra hne
        apply hbadw
        left
        simp only [Finset.mem_erase] at hw ⊢
        exact ⟨hne, hw⟩
      · have heq : u = x := by
          by_contra hne
          apply hbadw
          right
          refine ⟨u, ?_, hadj⟩
          simp only [Finset.mem_erase] at hu ⊢
          exact ⟨hne, hu⟩
        subst u
        exact Or.inr hadj
    have hvcov : w = v ∨ adj w v := by
      rcases hdom_x w with hw | ⟨u, hu, hadj⟩
      · left
        by_contra hne
        apply hbadw
        left
        simp only [Finset.mem_erase] at hw ⊢
        exact ⟨hw.1, hne, hw.2⟩
      · have heq : u = v := by
          by_contra hne
          apply hbadw
          right
          refine ⟨u, ?_, hadj⟩
          simp only [Finset.mem_erase] at hu ⊢
          exact ⟨hu.1, hne, hu.2⟩
        subst u
        exact Or.inr hadj
    refine ⟨w, Finset.Subset.antisymm ?_ ?_⟩
    · intro u hu
      obtain ⟨huS, hucov⟩ : u ∈ S ∧ (w = u ∨ adj w u) := by
        simpa only [footprint, Finset.mem_filter] using hu
      by_cases hux : u = x
      · simp [hux]
      by_cases huv : u = v
      · simp [huv]
      exact (no_other_cover u huS hux huv hucov).elim
    · intro u hu
      have hu' : u = x ∨ u = v := by simpa using hu
      rcases hu' with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hx, hxcov⟩
      · exact Finset.mem_filter.mpr ⟨hv, hvcov⟩
  · rintro ⟨w, hw⟩ hdom
    rcases hdom w with hmem | ⟨u, hu, hadj⟩
    · have hfp : w ∈ footprint adj S w := by
        apply Finset.mem_filter.mpr
        exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).2,
          Or.inl rfl⟩
      rw [hw] at hfp
      have heq : w = x ∨ w = v := by simpa using hfp
      rcases heq with hx' | hv'
      · exact (Finset.mem_erase.mp hmem).1 hx'
      · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).1 hv'
    · have hfp : u ∈ footprint adj S w := by
        apply Finset.mem_filter.mpr
        exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).2,
          Or.inr hadj⟩
      rw [hw] at hfp
      have heq : u = x ∨ u = v := by simpa using hfp
      rcases heq with hx' | hv'
      · exact (Finset.mem_erase.mp hu).1 hx'
      · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1 hv'

theorem critical_deletion_symmetric {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) (S : Finset α) (x v : α)
    (hdom_x : IsDominating adj (S.erase x))
    (hdom_v : IsDominating adj (S.erase v)) :
    (¬ IsDominating adj ((S.erase v).erase x)) ↔
      (¬ IsDominating adj ((S.erase x).erase v)) := by
  have hsets : (S.erase v).erase x = (S.erase x).erase v := by
    ext u
    simp only [Finset.mem_erase]
    tauto
  rw [hsets]

end GapThreeCriticalConflict
