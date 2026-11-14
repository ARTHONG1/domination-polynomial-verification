import Mathlib
import domination_gap3.GapFourFiniteReductionCandidate
import domination_gap3.ForestGapThreeAllNoIsolatesCandidate
import domination_gap3.GapFourForestLargeCandidate
import domination_gap3.GraphUniformGapCandidate
import domination_gap3.BipartiteCriticalIndependentCandidate
import domination_gap3.FiniteUniformVarianceCandidate

namespace RefereeAudit
open scoped BigOperators
open GapThreeGraphConnectionAudit

/-!
  1. Definition unification across all internal Lean namespaces
-/
theorem isDominating_defs_agree {α : Type*} (adj : α → α → Prop) (S : Finset α) :
    GapThreeGraphConnectionAudit.IsDominating adj S ↔
      GapThreeCriticalConflictCount.IsDominating adj S ∧
      (GapThreeGraphConnectionAudit.IsDominating adj S ↔
        GapThreeForestAcyclic.IsDominating adj S) ∧
      (GapThreeGraphConnectionAudit.IsDominating adj S ↔
        GapThreeGraphLevelSynthesisAudit.IsDominating adj S) := by
  simp [GapThreeGraphConnectionAudit.IsDominating,
    GapThreeCriticalConflictCount.IsDominating,
    GapThreeForestAcyclic.IsDominating,
    GapThreeGraphLevelSynthesisAudit.IsDominating]

theorem critical_defs_agree {α : Type*} [DecidableEq α]
    (adj : α → α → Prop)
    [i1 : DecidablePred (GapThreeGraphConnectionAudit.IsDominating adj)]
    [i2 : DecidablePred (GapThreeCriticalConflictCount.IsDominating adj)]
    (S : Finset α) :
    GapThreeGraphConnectionAudit.domCritical adj S =
      GapThreeCriticalConflictCount.critical adj S := by
  ext x
  simp [GapThreeGraphConnectionAudit.domCritical,
    GapThreeCriticalConflictCount.critical,
    GapThreeGraphConnectionAudit.IsDominating,
    GapThreeCriticalConflictCount.IsDominating]

/-!
  2. Non-vacuity audit: concrete star graph K_{1,4} on Fin 5 satisfies all hypotheses
     of forest_gap_three_unimodal_no_isolates
-/
def star5 : SimpleGraph (Fin 5) where
  Adj u v := (u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0)
  symm := by
    intro u v h
    rcases h with h | h <;> [exact Or.inr h; exact Or.inl h]
  loopless := by
    intro u h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h2 h1

theorem star5_no_isolates : ∀ v : Fin 5, ∃ u : Fin 5, star5.Adj v u := by
  intro v
  by_cases hv : v = 0
  · subst hv
    exact ⟨1, Or.inl ⟨rfl, by decide⟩⟩
  · exact ⟨0, Or.inr ⟨rfl, by intro h; apply hv; exact Fin.ext h⟩⟩

theorem star5_center_dominates : IsDominating star5.Adj ({0} : Finset (Fin 5)) := by
  intro v
  by_cases hv : v = 0
  · subst hv; exact Or.inl (by simp)
  · exact Or.inr ⟨0, by simp, Or.inr ⟨rfl, by intro h; apply hv; exact Fin.ext h⟩⟩

/-!
  3. Formal verification of unformalized Lemma 2.3 (unimodality equivalence under prepending r zeros)
-/
theorem unimodal_prepend_zeros (d0 : ℕ → ℝ) (r : ℕ)
    (hnonneg : ∀ k, 0 ≤ d0 k) :
    (∃ m : ℕ, (∀ k < m, (if k < r then 0 else d0 (k - r)) ≤ (if k + 1 < r then 0 else d0 (k + 1 - r))) ∧
      (∀ k ≥ m, (if k + 1 < r then 0 else d0 (k + 1 - r)) ≤ (if k < r then 0 else d0 (k - r)))) ↔
    (∃ m0 : ℕ, (∀ k < m0, d0 k ≤ d0 (k + 1)) ∧ (∀ k ≥ m0, d0 (k + 1) ≤ d0 k)) := by
  constructor
  · rintro ⟨m, hup, hdn⟩
    by_cases hmr : m < r
    · refine ⟨0, ?_, ?_⟩
      · intro k hk; omega
      · intro k _
        have hzero : ∀ t, d0 t = 0 := by
          intro t
          have hstep : ∀ s ≥ m, (if s < r then 0 else d0 (s - r)) ≤ 0 := by
            intro s hs
            induction s, hs using Nat.le_induction with
            | base => simp [hmr]
            | succ s hs ih => exact (hdn s hs).trans ih
          have hle := hstep (r + t) (by omega)
          have hnot : ¬ (r + t < r) := by omega
          have hsub : r + t - r = t := by omega
          rw [if_neg hnot, hsub] at hle
          linarith [hnonneg t]
        simp [hzero]
    · refine ⟨m - r, ?_, ?_⟩
      · intro k hk
        have h1 := hup (r + k) (by omega)
        have hn1 : ¬ (r + k < r) := by omega
        have hn2 : ¬ (r + k + 1 < r) := by omega
        have hs1 : r + k - r = k := by omega
        have hs2 : r + k + 1 - r = k + 1 := by omega
        simpa [hn1, hn2, hs1, hs2] using h1
      · intro k hk
        have h1 := hdn (r + k) (by omega)
        have hn1 : ¬ (r + k < r) := by omega
        have hn2 : ¬ (r + k + 1 < r) := by omega
        have hs1 : r + k - r = k := by omega
        have hs2 : r + k + 1 - r = k + 1 := by omega
        simpa [hn1, hn2, hs1, hs2] using h1
  · rintro ⟨m0, hup, hdn⟩
    refine ⟨r + m0, ?_, ?_⟩
    · intro k hk
      by_cases hkr : k + 1 < r
      · have hk0 : k < r := by omega
        simp [hk0, hkr]
      · by_cases hk0 : k < r
        · simp [hk0, hkr, hnonneg]
        · have hs1 : k + 1 - r = (k - r) + 1 := by omega
          simpa [hk0, hkr, hs1] using hup (k - r) (by omega)
    · intro k hk
      have hn1 : ¬ (k < r) := by omega
      have hn2 : ¬ (k + 1 < r) := by omega
      have hs1 : k + 1 - r = (k - r) + 1 := by omega
      simpa [hn1, hn2, hs1] using hdn (k - r) (by omega)

/-!
  4. Closing the h = 1 (K_1 = 1) and A + 2 > n boundary gaps in Lean:
     Lemma 4.3 WITHOUT h < K (using 0 < j - c directly from equation (5)),
     and short-tail unimodality when n < A + 2 (i.e. n - γ ≤ 2).
-/
theorem lemma_jump_without_h_lt_K (j γ h K c cprev v : ℝ)
    (hden : 0 < j - c)
    (hquad : (h + 1) ^ 2 ≤ 4 * K)
    (hj : γ + K ≤ j)
    (hvar : v ≤ (c - (2 * γ - j)) * (2 * γ - j + 2 * h - c))
    (hinc : (j - c) * (c - cprev) ≤ v) :
    c - cprev ≤ 2 := by
  have hsquare : 0 ≤ (c - (2 * γ - j) - (h + 1)) ^ 2 := sq_nonneg _
  have hidentity :
      2 * (j - c) - (c - (2 * γ - j)) * (2 * γ - j + 2 * h - c) =
        (c - (2 * γ - j) - (h + 1)) ^ 2 + 4 * (j - γ) - (h + 1) ^ 2 := by
    ring
  have hvar_bnd : v ≤ 2 * (j - c) := by linarith
  by_contra hn
  have hjump : 0 < c - cprev - 2 := by linarith
  have hpos := mul_pos hden hjump
  nlinarith

theorem short_tail_unimodal (d : ℕ → ℝ) (A n : ℕ)
    (hshort : n ≤ A + 1)
    (hnonneg : ∀ k, 0 ≤ d k)
    (hzero : ∀ k, n < k → d k = 0)
    (hleft : ∀ k < A, d k ≤ d (k + 1)) :
    ∃ m : ℕ, (∀ k < m, d k ≤ d (k + 1)) ∧ (∀ k ≥ m, d (k + 1) ≤ d k) := by
  by_cases hnA : n ≤ A
  · refine ⟨n, ?_, ?_⟩
    · intro k hk; exact hleft k (lt_of_lt_of_le hk hnA)
    · intro k hk
      rw [hzero (k + 1) (by omega)]
      exact hnonneg k
  · have hnEq : n = A + 1 := by omega
    by_cases hstep : d A ≤ d (A + 1)
    · refine ⟨A + 1, ?_, ?_⟩
      · intro k hk
        by_cases hkA : k < A
        · exact hleft k hkA
        · have : k = A := by omega
          subst k; exact hstep
      · intro k hk
        rw [hzero (k + 1) (by omega)]
        exact hnonneg k
    · refine ⟨A, hleft, ?_⟩
      intro k hk
      by_cases hkEq : k = A
      · subst k; linarith
      · rw [hzero (k + 1) (by omega)]
        exact hnonneg k

#print axioms isDominating_defs_agree
#print axioms critical_defs_agree
#print axioms unimodal_prepend_zeros
#print axioms lemma_jump_without_h_lt_K
#print axioms short_tail_unimodal

end RefereeAudit

