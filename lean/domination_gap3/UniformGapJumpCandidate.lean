import Mathlib

namespace UniformGapJumpAudit

theorem uniform_gap_mean_jump (j γ h K c cprev v : ℝ)
    (hK : h < K) (hquad : (h + 1) ^ 2 ≤ 4 * K)
    (hj : γ + K ≤ j)
    (hc_low : 2 * γ - j ≤ c)
    (hc_high : c ≤ 2 * γ - j + 2 * h)
    (hvar : v ≤ (c - (2 * γ - j)) * (2 * γ - j + 2 * h - c))
    (hinc : (j - c) * (c - cprev) ≤ v) :
    c - cprev ≤ 2 := by
  have hden : 0 < j - c := by linarith
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

theorem nonincrease_then_rise_forces_jump
    (n i dprev di dnext ci cnext : ℝ)
    (hdi : 0 < di) (hdnext : 0 < dnext) (hin : i < n)
    (hid_i : di * (i - ci) = (n - i + 1) * dprev)
    (hid_next : dnext * (i + 1 - cnext) = (n - i) * di)
    (h_nonincrease : di ≤ dprev) (h_rise : di < dnext) :
    2 < cnext - ci := by
  have hfactor : 0 < n - i := by linarith
  have hfactor1 : 0 ≤ n - i + 1 := by linarith
  have hprev : (n - i + 1) * di ≤ (n - i + 1) * dprev :=
    mul_le_mul_of_nonneg_left h_nonincrease hfactor1
  have hnext : (n - i) * di < (n - i) * dnext :=
    mul_lt_mul_of_pos_left h_rise hfactor
  have hci_mul : di * (ci - (2 * i - n - 1)) ≤ 0 := by nlinarith [hid_i, hprev]
  have hci : ci ≤ 2 * i - n - 1 := by
    by_contra hc
    have hp : 0 < di * (ci - (2 * i - n - 1)) :=
      mul_pos hdi (by linarith)
    linarith
  have hcnext_mul : 0 < dnext * (cnext - (2 * i + 1 - n)) := by
    nlinarith [hid_next, hnext]
  have hcnext : 2 * i + 1 - n < cnext := by
    by_contra hc
    have hp : dnext * (cnext - (2 * i + 1 - n)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdnext) (by linarith)
    linarith
  linarith

theorem weak_unimodal_of_no_rebound
    (d : ℕ → ℝ) (A n : ℕ)
    (hAn : A ≤ n)
    (h_left : ∀ k < A, d k ≤ d (k + 1))
    (h_drop : d (n + 1) < d n)
    (h_no_rebound : ∀ k ≥ A, d (k + 1) ≤ d k → d (k + 2) ≤ d (k + 1)) :
    ∃ m : ℕ, (∀ k < m, d k ≤ d (k + 1)) ∧
      (∀ k ≥ m, d (k + 1) ≤ d k) := by
  let P : ℕ → Prop := fun k => A ≤ k ∧ d (k + 1) < d k
  have h_exists : ∃ k : ℕ, P k := ⟨n, hAn, h_drop⟩
  let m := Nat.find h_exists
  have hm : P m := Nat.find_spec h_exists
  refine ⟨m, ?_, ?_⟩
  · intro k hk
    by_cases hAk : A ≤ k
    · by_contra hc
      have hlt : d (k + 1) < d k := lt_of_not_ge hc
      exact (Nat.find_min h_exists hk) ⟨hAk, hlt⟩
    · exact h_left k (by omega)
  · intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hm.2.le
    | succ k hk ih =>
      exact h_no_rebound k (le_trans hm.1 hk) ih

end UniformGapJumpAudit
