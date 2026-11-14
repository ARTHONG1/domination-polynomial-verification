import Mathlib

/-! Candidate for the submitted general-h paper arithmetic exactly. -/

namespace FinalVerificationGapArithmetic

def K (h : ℕ) : ℕ := ((h + 1)^2 + 3) / 4

theorem K_is_ceil (h : ℕ) :
    (h + 1)^2 ≤ 4 * K h ∧ 4 * K h < (h + 1)^2 + 4 := by
  dsimp [K]
  omega

theorem K_numeric :
    K 0 = 1 ∧ K 1 = 1 ∧ K 2 = 3 ∧ K 3 = 4 ∧ K 4 = 7 ∧ K 5 = 9 := by
  norm_num [K]

theorem source_condition_floor_iff (n γ k : ℕ) (hγn : γ ≤ n) :
    γ + 3 * k ≤ n + 7 ↔ k ≤ (n - γ + 1) / 3 + 2 := by
  omega

theorem h_must_be_three (n h : ℕ) (hn : 1 ≤ n)
    (hnonunimodal_bound : n + h + 16 ≤ 6 * K h) : 3 ≤ h := by
  by_contra hh
  have hh2 : h ≤ 2 := by omega
  interval_cases h <;> norm_num [K] at hnonunimodal_bound <;> omega

theorem quadratic_excludes_nonunimodality (n h : ℕ)
    (hquad : 3 * h ^ 2 + 4 * h ≤ 2 * n + 19) :
    6 * K h < n + h + 16 := by
  have hK : 4 * K h ≤ (h + 1)^2 + 3 := by
    dsimp [K]
    omega
  have hh : (h+1)^2 = h^2 + 2*h + 1 := by ring
  rw [hh] at hK
  omega

#print axioms K_is_ceil
#print axioms K_numeric
#print axioms source_condition_floor_iff
#print axioms h_must_be_three
#print axioms quadratic_excludes_nonunimodality

end FinalVerificationGapArithmetic
