import Mathlib

/-! Submitted Lemma 4.3's last analytic step.  Unlike the older
UniformGapJumpCandidate lemma, the proof needs only j-c_j>0, not h<K_h.
This is a new fixed target; the result by itself does not prove Theorem 5.1. -/

namespace FinalVerificationMeanJumpNoStrict

theorem mean_jump_without_h_lt_K
    (j γ h K c cprev v : ℝ)
    (hquad : (h+1)^2 ≤ 4*K)
    (hj : γ+K ≤ j)
    (hden : 0 < j-c)
    (hc_low : 2*γ-j ≤ c)
    (hc_high : c ≤ 2*γ-j+2*h)
    (hvar : v ≤ (c-(2*γ-j))*(2*γ-j+2*h-c))
    (hinc : (j-c)*(c-cprev) ≤ v) :
    c-cprev ≤ 2 := by
  sorry

end FinalVerificationMeanJumpNoStrict
