import Mathlib

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
  have hsquare : 0 ≤ (c-(2*γ-j)-(h+1))^2 := sq_nonneg _
  have hidentity :
      2*(j-c)-(c-(2*γ-j))*(2*γ-j+2*h-c) =
        (c-(2*γ-j)-(h+1))^2 + 4*(j-γ)-(h+1)^2 := by
    ring
  have hvbound : v ≤ 2*(j-c) := by nlinarith
  by_contra hbad
  have hpositive : 0 < c-cprev-2 := by linarith
  have hprod : 0 < (j-c)*(c-cprev-2) := mul_pos hden hpositive
  nlinarith

#print axioms mean_jump_without_h_lt_K

end FinalVerificationMeanJumpNoStrict
