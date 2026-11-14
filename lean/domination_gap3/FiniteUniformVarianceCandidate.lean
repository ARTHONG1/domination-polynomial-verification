import Mathlib

namespace FiniteUniformVarianceAudit

/-- Bounded-population variance inequality for the uniform measure on a nonempty finite set. -/
theorem finite_uniform_variance_bound
    {α : Type*} (s : Finset α) (a : α → ℝ) (L U : ℝ)
    (hs : s.Nonempty)
    (hb : ∀ x ∈ s, L ≤ a x ∧ a x ≤ U) :
    let μ := (∑ x ∈ s, a x) / (s.card : ℝ)
    L ≤ μ ∧ μ ≤ U ∧
      (∑ x ∈ s, (a x - μ) ^ 2) / (s.card : ℝ) ≤ (μ - L) * (U - μ) := by
  dsimp
  let μ : ℝ := (∑ x ∈ s, a x) / (s.card : ℝ)
  have hd : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hμ : (∑ x ∈ s, a x) = (s.card : ℝ) * μ := by
    dsimp [μ]
    field_simp
  have hlow_sum : (s.card : ℝ) * L ≤ ∑ x ∈ s, a x := by
    have h := Finset.sum_le_sum (s := s) (fun x hx => (hb x hx).1)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using h
  have hupp_sum : (∑ x ∈ s, a x) ≤ (s.card : ℝ) * U := by
    have h := Finset.sum_le_sum (s := s) (fun x hx => (hb x hx).2)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using h
  have hμlo : L ≤ μ := by nlinarith
  have hμhi : μ ≤ U := by nlinarith
  have hzero : (∑ x ∈ s, (a x - μ)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hμ]
    ring
  have hp : ∀ x ∈ s,
      (a x - μ) ^ 2 ≤ (μ - L) * (U - μ) +
        (a x - μ) * (L + U - 2 * μ) := by
    intro x hx
    rcases hb x hx with ⟨hxL, hxU⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hxL) (sub_nonneg.mpr hxU)]
  have hsum : (∑ x ∈ s, (a x - μ) ^ 2) ≤ (s.card : ℝ) * ((μ - L) * (U - μ)) := by
    calc
      (∑ x ∈ s, (a x - μ) ^ 2) ≤
          ∑ x ∈ s, ((μ - L) * (U - μ) +
            (a x - μ) * (L + U - 2 * μ)) := Finset.sum_le_sum hp
      _ = (s.card : ℝ) * ((μ - L) * (U - μ)) +
          (∑ x ∈ s, (a x - μ)) * (L + U - 2 * μ) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          nsmul_eq_mul, mul_comm, ← Finset.sum_mul]
      _ = (s.card : ℝ) * ((μ - L) * (U - μ)) := by rw [hzero]; ring
  refine ⟨hμlo, hμhi, ?_⟩
  dsimp [μ] at *
  exact (div_le_iff₀ hd).2 (by nlinarith)

end FiniteUniformVarianceAudit
