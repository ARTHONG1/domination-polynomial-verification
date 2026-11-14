import Mathlib

/-! Frozen arithmetic consequences of the general-h conditions in the
submitted Theorem 5.1 and Theorem 1.2. -/

namespace FinalVerificationGapArithmetic

def K (h : ℕ) : ℕ := ((h + 1)^2 + 3) / 4

theorem K_is_ceil (h : ℕ) :
    (h + 1)^2 ≤ 4 * K h ∧ 4 * K h < (h + 1)^2 + 4 := by
  sorry

theorem K_numeric :
    K 0 = 1 ∧ K 1 = 1 ∧ K 2 = 3 ∧ K 3 = 4 ∧ K 4 = 7 ∧ K 5 = 9 := by
  sorry

theorem source_condition_floor_iff (n γ k : ℕ) (hγn : γ ≤ n) :
    γ + 3 * k ≤ n + 7 ↔ k ≤ (n - γ + 1) / 3 + 2 := by
  sorry

theorem h_must_be_three (n h : ℕ) (hn : 1 ≤ n)
    (hnonunimodal_bound : n + h + 16 ≤ 6 * K h) : 3 ≤ h := by
  sorry

theorem quadratic_excludes_nonunimodality (n h : ℕ)
    (hquad : 3 * h ^ 2 + 4 * h ≤ 2 * n + 19) :
    6 * K h < n + h + 16 := by
  sorry

end FinalVerificationGapArithmetic
