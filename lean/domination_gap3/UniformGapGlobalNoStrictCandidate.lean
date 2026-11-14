import Mathlib
import domination_gap3.UniformGapJumpCandidate
import domination_gap3.FinalVerificationMeanJumpNoStrictCandidate

namespace UniformGapGlobalNoStrictAudit

/-- Global bounded-gap unimodality from rank identities, critical-moment data,
and eventual zero coefficients. Both plateaus and arbitrary widths h are included.
The published tree-specific critical-vertex bounds are inputs, not proved here. -/
theorem weak_unimodal_of_uniform_rank_data
    (d c v : ℕ → ℝ) (n A γ h K : ℕ)
    (hquad : (h + 1) ^ 2 ≤ 4 * K)
    (hcut : γ + K ≤ A + 2) (hAn : A + 2 ≤ n)
    (hleft : ∀ k < A, d k ≤ d (k + 1))
    (hpos : ∀ j, A + 1 ≤ j → j ≤ n → 0 < d j)
    (hnonneg : ∀ j, 0 ≤ d j)
    (hzero : ∀ j, n < j → d j = 0)
    (hid : ∀ i, i + 1 ≤ n →
      d (i + 1) * (((i + 1 : ℕ) : ℝ) - c (i + 1)) =
        ((n : ℝ) - (i : ℝ)) * d i)
    (hmean : ∀ j, γ + K ≤ j → j ≤ n →
      2 * (γ : ℝ) - (j : ℝ) ≤ c j ∧
      c j ≤ 2 * (γ : ℝ) - (j : ℝ) + 2 * (h : ℝ))
    (hvar : ∀ j, γ + K ≤ j → j ≤ n →
      v j ≤ (c j - (2 * (γ : ℝ) - (j : ℝ))) *
        (2 * (γ : ℝ) - (j : ℝ) + 2 * (h : ℝ) - c j))
    (hinc : ∀ j, γ + K ≤ j → j ≤ n →
      ((j : ℝ) - c j) * (c j - c (j - 1)) ≤ v j)
    (hden : ∀ j, γ + K ≤ j → j ≤ n → 0 < (j : ℝ) - c j) :
    ∃ m : ℕ, (∀ k < m, d k ≤ d (k + 1)) ∧
      (∀ k ≥ m, d (k + 1) ≤ d k) := by
  have hdrop : d (n + 1) < d n := by
    rw [hzero (n + 1) (by omega)]
    exact hpos n (by omega) le_rfl
  apply UniformGapJumpAudit.weak_unimodal_of_no_rebound d A n (by omega) hleft hdrop
  intro k hk hnon
  by_cases hwithin : k + 2 ≤ n
  · have hj : γ + K ≤ k + 2 := by omega
    have hi_pos : 0 < d (k + 1) := hpos (k + 1) (by omega) (by omega)
    have hj_pos : 0 < d (k + 2) := hpos (k + 2) (by omega) hwithin
    have hm := hmean (k + 2) hj hwithin
    have hv := hvar (k + 2) hj hwithin
    have hc := hinc (k + 2) hj hwithin
    have hcast : (k + 2 - 1 : ℕ) = k + 1 := by omega
    rw [hcast] at hc
    have hquadreal : ((h : ℝ) + 1) ^ 2 ≤ 4 * (K : ℝ) := by exact_mod_cast hquad
    have hjreal : (γ : ℝ) + (K : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast hj
    have hmean_jump : c (k + 2) - c (k + 1) ≤ 2 :=
      FinalVerificationMeanJumpNoStrict.mean_jump_without_h_lt_K _ _ _ _ _ _ _
        hquadreal hjreal (hden (k + 2) hj hwithin) hm.1 hm.2 hv hc
    by_contra hr
    have hrise : d (k + 1) < d (k + 2) := lt_of_not_ge hr
    have hin : ((k + 1 : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hwithin
    have hid1 : d (k + 1) * (((k + 1 : ℕ) : ℝ) - c (k + 1)) =
        ((n : ℝ) - ((k + 1 : ℕ) : ℝ) + 1) * d k := by
      have eq := hid k (by omega)
      convert eq using 1 <;> push_cast <;> ring
    have hid2 : d (k + 2) * (((k + 1 : ℕ) : ℝ) + 1 - c (k + 2)) =
        ((n : ℝ) - ((k + 1 : ℕ) : ℝ)) * d (k + 1) := by
      have eq := hid (k + 1) (by omega)
      convert eq using 1 <;> push_cast <;> ring
    have hbig := UniformGapJumpAudit.nonincrease_then_rise_forces_jump
      (n : ℝ) ((k + 1 : ℕ) : ℝ) (d k) (d (k + 1)) (d (k + 2))
      (c (k + 1)) (c (k + 2)) hi_pos hj_pos hin hid1 hid2 hnon hrise
    linarith
  · have hout : n < k + 2 := by omega
    rw [hzero (k + 2) hout]
    exact hnonneg (k + 1)

end UniformGapGlobalNoStrictAudit
