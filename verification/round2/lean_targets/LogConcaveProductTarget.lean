import Mathlib

/-!
Fixed statements for Lemma 6.2 of the manuscript and for the unimodality step
used in Corollary 6.3. The proofs are in
lean/domination_gap3/LogConcaveProductCandidate.lean.

Correspondence with the manuscript.
* A polynomial with real coefficients is a term of Polynomial ℝ; its
  coefficient sequence is p.coeff : ℕ → ℝ, which vanishes beyond the degree.
* PolynomialTuran p is d_j^2 ≥ d_(j-1) d_(j+1) for every j ≥ 1. Beyond the
  degree the right-hand side is 0, so this is the manuscript's log-concavity.
* PolynomialGapless p says that the support is an interval (no internal zeros).
* Nonnegativity is stated as a separate hypothesis.
No hypothesis is added to those printed in the manuscript.
-/

namespace LogConcaveProduct

/-- Ordinary finite polynomial Turán inequalities, including the leading
and trailing boundary where one coefficient may vanish. -/
def PolynomialTuran (p : Polynomial ℝ) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    p.coeff (j-1)*p.coeff (j+1) ≤ (p.coeff j)^2

def PolynomialGapless (p : Polynomial ℝ) : Prop :=
  ∀ a b c : ℕ, a < b → b < c →
    0 < p.coeff a → 0 < p.coeff c → 0 < p.coeff b

/-- Lemma 6.2. -/
theorem polynomial_real_mul_nonnegative_logconcave_gapless
    (p q : Polynomial ℝ)
    (hpn : ∀ j : ℕ, 0 ≤ p.coeff j)
    (hpt : PolynomialTuran p) (hpg : PolynomialGapless p)
    (hqn : ∀ j : ℕ, 0 ≤ q.coeff j)
    (hqt : PolynomialTuran q) (hqg : PolynomialGapless q) :
    (∀ j : ℕ, 0 ≤ (p*q).coeff j) ∧
      PolynomialTuran (p*q) ∧ PolynomialGapless (p*q) := by
  sorry

/-- A nonnegative log-concave coefficient sequence without internal zeros is
unimodal (used in the proof of Corollary 6.3). -/
theorem polynomial_logconcave_gapless_unimodal
    (p : Polynomial ℝ)
    (hnon : ∀ j : ℕ, 0 ≤ p.coeff j)
    (hlc : PolynomialTuran p)
    (hgap : PolynomialGapless p) :
    ∃ m : ℕ, (∀ k < m, p.coeff k ≤ p.coeff (k+1)) ∧
      (∀ k ≥ m, p.coeff (k+1) ≤ p.coeff k) := by
  sorry

end LogConcaveProduct
