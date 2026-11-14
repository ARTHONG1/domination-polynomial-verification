import Mathlib

namespace FinalVerificationP24TopAlgebra

noncomputable def b (n L : ℝ) : ℝ := n * (n - 1) / 2 - L
noncomputable def u (n L : ℝ) : ℝ := n * (n - 1) * (n - 2) / 6 - L * (n - 2) + L * (L - 1) / 2

theorem exact_factorization (n L : ℝ) :
    2 * b n L * (b n L - 1) - 3 * n * u n L =
      (n - 1 - L) * (L * (3 * n - 4) + n * (n - 2)) / 2 := by
  unfold b u
  ring

theorem top_bound_and_star_equality (n L : ℝ)
    (hn : 5 ≤ n) (hL : 0 ≤ L) (hLmax : L ≤ n - 1) :
    3 * n * u n L ≤ 2 * b n L * (b n L - 1) ∧
      (3 * n * u n L = 2 * b n L * (b n L - 1) ↔ L = n - 1) := by
  have hfactor : 0 < L * (3 * n - 4) + n * (n - 2) := by
    have ha : 0 ≤ L * (3 * n - 4) := mul_nonneg hL (by linarith)
    have hb : 0 < n * (n - 2) := mul_pos (by linarith) (by linarith)
    linarith
  have hdecomp := exact_factorization n L
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ n - 1 - L by linarith) (le_of_lt hfactor)]
  · constructor
    · intro heq
      have heq0 : (n - 1 - L) * (L * (3 * n - 4) + n * (n - 2)) = 0 := by
        nlinarith [hdecomp]
      have hzero := (mul_eq_zero.mp heq0)
      rcases hzero with hz | hz
      · linarith
      · exact False.elim ((ne_of_gt hfactor) hz)
    · intro hstar
      rw [hstar] at hdecomp ⊢
      nlinarith

#print axioms exact_factorization
#print axioms top_bound_and_star_equality

end FinalVerificationP24TopAlgebra
