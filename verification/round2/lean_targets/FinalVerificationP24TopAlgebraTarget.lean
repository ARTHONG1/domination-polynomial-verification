import Mathlib

/-! Submitted Section 7: the exact algebraic factorization for the top
coefficients and its equality condition. The combinatorial bounds on
d_(n-2), d_(n-3) are separate obligations. -/

namespace FinalVerificationP24TopAlgebra

noncomputable def b (n L : ℝ) : ℝ := n * (n - 1) / 2 - L
noncomputable def u (n L : ℝ) : ℝ := n * (n - 1) * (n - 2) / 6 - L * (n - 2) + L * (L - 1) / 2

theorem exact_factorization (n L : ℝ) :
    2 * b n L * (b n L - 1) - 3 * n * u n L =
      (n - 1 - L) * (L * (3 * n - 4) + n * (n - 2)) / 2 := by
  sorry

theorem top_bound_and_star_equality (n L : ℝ)
    (hn : 5 ≤ n) (hL : 0 ≤ L) (hLmax : L ≤ n - 1) :
    3 * n * u n L ≤ 2 * b n L * (b n L - 1) ∧
      (3 * n * u n L = 2 * b n L * (b n L - 1) ↔ L = n - 1) := by
  sorry

end FinalVerificationP24TopAlgebra
