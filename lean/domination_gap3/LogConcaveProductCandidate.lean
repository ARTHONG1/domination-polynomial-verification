import Mathlib

/-!
# Lemma 6.2 and the unimodality step of Corollary 6.3

Self-contained (Mathlib only) Lean 4 proof of the two facts about coefficient
sequences that the manuscript uses in Section 6.

* `polynomial_real_mul_nonnegative_logconcave_gapless` (Lemma 6.2): if two real
  polynomials have nonnegative, log-concave coefficient sequences without
  internal zeros, then so does their product.
* `polynomial_logconcave_gapless_unimodal`: such a coefficient sequence is
  unimodal.

The proof of the first statement follows the manuscript: adjacent log-concavity
and the absence of internal zeros give all 2x2 Toeplitz minors (TP2), and the
two-row Cauchy--Binet identity carries TP2 through convolution.

The statements are fixed, with `sorry` in place of the proofs, in
verification/round2/lean_targets/LogConcaveProductTarget.lean.
-/

namespace LogConcaveProduct

/-- The finite two-row Cauchy–Binet identity, in the form needed to
transfer Toeplitz minors through coefficient convolution. -/
theorem two_row_product_identity {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u v a b : ι → ℝ) :
    (∑ i ∈ s, ∑ k ∈ s,
      (u i * v k - u k * v i) * (a i * b k - a k * b i)) =
      2 * ((∑ i ∈ s, u i * a i) * (∑ k ∈ s, v k * b k) -
        (∑ i ∈ s, u i * b i) * (∑ k ∈ s, v k * a k)) := by
  have hdistrib (f g : ι → ℝ) :
      (∑ i ∈ s, ∑ k ∈ s, f i * g k) =
        (∑ i ∈ s, f i) * (∑ k ∈ s, g k) := by
    calc
      _ = ∑ i ∈ s, f i * (∑ k ∈ s, g k) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  calc
    _ = (∑ i ∈ s, ∑ k ∈ s,
         ((u i * a i) * (v k * b k) -
          (u i * b i) * (v k * a k) -
          (v i * a i) * (u k * b k) +
          (v i * b i) * (u k * a k))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∑ i ∈ s, ∑ k ∈ s, (u i * a i) * (v k * b k)) -
        (∑ i ∈ s, ∑ k ∈ s, (u i * b i) * (v k * a k)) -
        (∑ i ∈ s, ∑ k ∈ s, (v i * a i) * (u k * b k)) +
        (∑ i ∈ s, ∑ k ∈ s, (v i * b i) * (u k * a k)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = 2 * ((∑ i ∈ s, u i * a i) * (∑ k ∈ s, v k * b k) -
        (∑ i ∈ s, u i * b i) * (∑ k ∈ s, v k * a k)) := by
      rw [hdistrib, hdistrib]
      have h3 : (∑ i ∈ s, ∑ k ∈ s, (v i * a i) * (u k * b k)) =
          (∑ i ∈ s, u i * b i) * (∑ k ∈ s, v k * a k) := by
        rw [hdistrib]
        ring
      have h4 : (∑ i ∈ s, ∑ k ∈ s, (v i * b i) * (u k * a k)) =
          (∑ i ∈ s, u i * a i) * (∑ k ∈ s, v k * b k) := by
        rw [hdistrib]
        ring
      rw [h3,h4]
      ring

/-- If two families of two-by-two minors are pairwise sign-aligned, the
coefficient convolution minor is nonnegative. -/
theorem two_row_product_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u v a b : ι → ℝ)
    (h : ∀ i ∈ s, ∀ k ∈ s,
      0 ≤ (u i * v k - u k * v i) * (a i * b k - a k * b i)) :
    (∑ i ∈ s, u i * b i) * (∑ k ∈ s, v k * a k) ≤
      (∑ i ∈ s, u i * a i) * (∑ k ∈ s, v k * b k) := by
  have hsum : 0 ≤ ∑ i ∈ s, ∑ k ∈ s,
      (u i * v k - u k * v i) * (a i * b k - a k * b i) :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun k hk => h i hi k hk
  rw [two_row_product_identity] at hsum
  nlinarith

open scoped Classical

/-- A bi-infinite sequence has nonnegative coefficients. -/
def Nonnegative (f : ℤ → ℝ) : Prop := ∀ i, 0 ≤ f i

/-- Adjacent Turán inequalities. -/
def Turan (f : ℤ → ℝ) : Prop :=
  ∀ i, f (i-1) * f (i+1) ≤ (f i)^2

/-- No internal zero in the positive support. -/
def Gapless (f : ℤ → ℝ) : Prop :=
  ∀ a b c, a < b → b < c → 0 < f a → 0 < f c → 0 < f b

/-- Total positivity of order two for the bilateral Toeplitz matrix. -/
def ToeplitzTP2 (f : ℤ → ℝ) : Prop :=
  ∀ r₁ r₂ c₁ c₂ : ℤ, r₁ < r₂ → c₁ < c₂ →
    0 ≤ f (r₁-c₁)*f (r₂-c₂)-f (r₁-c₂)*f (r₂-c₁)

/-- Adjacent Turán plus gapless positive support implies monotonicity of
the adjacent ratio at every finite separation; no division is used. -/
private theorem adjacent_ratio_span (f : ℤ → ℝ)
    (hnon : Nonnegative f) (hlc : Turan f) (hgap : Gapless f)
    (d : ℕ) (a : ℤ) :
    f a * f (a + (d:ℤ) + 2) ≤ f (a+1) * f (a + (d:ℤ) + 1) := by
  induction d with
  | zero =>
    have hh := hlc (a+1)
    simpa [show (a+1)-1=a by omega, show (a+1)+1=a+2 by omega,
      pow_two] using hh
  | succ d ih =>
    let b : ℤ := a + (d:ℤ) + 2
    have hab : a < b := by dsimp [b]; omega
    have hprev : f a * f b ≤ f (a+1)*f (b-1) := by
      convert ih using 1 <;> congr 2 <;> dsimp [b] <;> omega
    have hnew : f a * f (b+1) ≤ f (a+1)*f b := by
      by_cases ha : f a = 0
      · rw [ha, zero_mul]
        exact mul_nonneg (hnon _) (hnon _)
      by_cases hc : f (b+1) = 0
      · rw [hc, mul_zero]
        exact mul_nonneg (hnon _) (hnon _)
      have hapos : 0 < f a := lt_of_le_of_ne (hnon _) (Ne.symm ha)
      have hcpos : 0 < f (b+1) := lt_of_le_of_ne (hnon _) (Ne.symm hc)
      have hbpos : 0 < f b := hgap a b (b+1) hab (by omega) hapos hcpos
      have hcurv := hlc b
      have hscaled :
          f b * (f a * f (b+1)) ≤ f b * (f (a+1)*f b) := by
        calc
          _ = (f a*f b)*f (b+1) := by ring
          _ ≤ (f (a+1)*f (b-1))*f (b+1) :=
            mul_le_mul_of_nonneg_right hprev (hnon _)
          _ = f (a+1)*(f (b-1)*f (b+1)) := by ring
          _ ≤ f (a+1)*((f b)^2) :=
            mul_le_mul_of_nonneg_left hcurv (hnon _)
          _ = f b*(f (a+1)*f b) := by ring
      exact (mul_le_mul_iff_of_pos_left hbpos).mp hscaled
    convert hnew using 1 <;> congr 2 <;> dsimp [b] <;> push_cast <;> ring

private theorem adjacent_ratio (f : ℤ → ℝ)
    (hnon : Nonnegative f) (hlc : Turan f) (hgap : Gapless f)
    (a b : ℤ) (hab : a < b) :
    f a * f (b+1) ≤ f (a+1)*f b := by
  have hn : 0 ≤ b-a-1 := by omega
  let d := (b-a-1).toNat
  have hd : (d:ℤ) = b-a-1 := Int.toNat_of_nonneg hn
  have h := adjacent_ratio_span f hnon hlc hgap d a
  convert h using 1 <;> congr 2 <;> dsimp [d] <;> rw [hd] <;> omega

/-- Finite shifts preserve the two-point inequality, without divisions. -/
private theorem ratio_shift (f : ℤ → ℝ)
    (hnon : Nonnegative f) (hlc : Turan f) (hgap : Gapless f)
    (d : ℕ) (a b : ℤ) (hab : a ≤ b) :
    f a * f (b+(d:ℤ)) ≤ f (a+(d:ℤ))*f b := by
  induction d generalizing a b with
  | zero => simp
  | succ d ih =>
    by_cases heq : a = b
    · subst b
      exact le_of_eq (mul_comm _ _)
    have hlt : a < b := lt_of_le_of_ne hab heq
    have hratio := adjacent_ratio f hnon hlc hgap a (b+(d:ℤ)) (by omega)
    have hshift := ih (a+1) b (by omega)
    have hfinal :
      f a * f (b+(d:ℤ)+1) ≤ f (a+(d:ℤ)+1)*f b := by
      calc
        _ ≤ f (a+1)*f (b+(d:ℤ)) := hratio
        _ ≤ f ((a+1)+(d:ℤ))*f b := hshift
        _ = _ := by ring
    convert hfinal using 1 <;> congr 2 <;> push_cast <;> ring

/-- For a nonnegative, gapless sequence, *all* Toeplitz minors follow
from the adjacent Turán inequalities. -/
theorem toeplitzTP2_of_turan (f : ℤ → ℝ)
    (hnon : Nonnegative f) (hlc : Turan f) (hgap : Gapless f) :
    ToeplitzTP2 f := by
  intro r₁ r₂ c₁ c₂ hr hc
  let delta : ℕ := (c₂-c₁).toNat
  have hdelta : (delta:ℤ) = c₂-c₁ := Int.toNat_of_nonneg (by omega)
  have h := ratio_shift f hnon hlc hgap delta (r₁-c₂) (r₂-c₂) (by omega)
  have ha : r₁-c₂+(delta:ℤ)=r₁-c₁ := by omega
  have hb : r₂-c₂+(delta:ℤ)=r₂-c₁ := by omega
  rw [ha, hb] at h
  nlinarith

/-- Convolution with a finitely supported real sequence. -/
noncomputable def finiteConv (f : ℤ → ℝ) (g : ℤ →₀ ℝ) (n : ℤ) : ℝ :=
  ∑ i ∈ g.support, f (n-i) * g i

/-- A translated support provides one finite index set for every entry
in the two-row Cauchy--Binet identity. -/
private theorem conv_sum_translated (f : ℤ → ℝ) (g : ℤ →₀ ℝ)
    (r c : ℤ) (s : Finset ℤ)
    (hcover : ∀ i ∈ g.support, i+c ∈ s) :
    finiteConv f g (r-c) = ∑ k ∈ s, f (r-k)*g (k-c) := by
  classical
  let shifted : Finset ℤ := g.support.image (fun i => i+c)
  have hsub : shifted ⊆ s := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact hcover i hi
  have hzero : ∀ k ∈ s, k ∉ shifted → f (r-k)*g (k-c) = 0 := by
    intro k hks hk
    have hg : g (k-c) = 0 := by
      by_contra hn
      have hi : k-c ∈ g.support := Finsupp.mem_support_iff.mpr hn
      apply hk
      exact Finset.mem_image.mpr ⟨k-c, hi, by omega⟩
    simp [hg]
  calc
    finiteConv f g (r-c) = ∑ i ∈ g.support, f (r-(i+c))*g i := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      congr 1
      omega
    _ = ∑ k ∈ shifted, f (r-k)*g (k-c) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i hi
        have hidx : i+c-c=i := by omega
        rw [hidx]
      · intro i hi j hj hij
        exact add_right_cancel hij
    _ = ∑ k ∈ s, f (r-k)*g (k-c) :=
      Finset.sum_subset hsub hzero

/-- Cauchy--Binet proves that convolution with a finitely supported
Toeplitz-TP2 sequence preserves *all* two-by-two Toeplitz minors. -/
theorem finiteConv_toeplitzTP2 (f : ℤ → ℝ) (g : ℤ →₀ ℝ)
    (hf : ToeplitzTP2 f)
    (hg : ToeplitzTP2 (fun i : ℤ => g i)) :
    ToeplitzTP2 (finiteConv f g) := by
  intro r₁ r₂ c₁ c₂ hr hc
  classical
  let s := (g.support.image (fun i => i+c₁)) ∪
    (g.support.image (fun i => i+c₂))
  have hcov1 : ∀ i ∈ g.support, i+c₁ ∈ s := by
    intro i hi
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hcov2 : ∀ i ∈ g.support, i+c₂ ∈ s := by
    intro i hi
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hpair : ∀ i ∈ s, ∀ k ∈ s,
      0 ≤ (f (r₁-i)*f (r₂-k)-f (r₁-k)*f (r₂-i)) *
        (g (i-c₁)*g (k-c₂)-g (k-c₁)*g (i-c₂)) := by
    intro i hi k hk
    rcases lt_trichotomy i k with hik | heq | hki
    · have hgm : 0 ≤ g (i-c₁)*g (k-c₂)-g (k-c₁)*g (i-c₂) := by
        nlinarith [hg i k c₁ c₂ hik hc]
      exact mul_nonneg (hf r₁ r₂ i k hr hik) hgm
    · subst k
      simp
    · have hf' := hf r₁ r₂ k i hr hki
      have hg' := hg k i c₁ c₂ hki hc
      have hfneg : f (r₁-i)*f (r₂-k)-f (r₁-k)*f (r₂-i) ≤ 0 := by
        nlinarith
      have hgneg : g (i-c₁)*g (k-c₂)-g (k-c₁)*g (i-c₂) ≤ 0 := by
        nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos hfneg hgneg
  have hCB := two_row_product_nonneg s
    (fun i => f (r₁-i)) (fun i => f (r₂-i))
    (fun i => g (i-c₁)) (fun i => g (i-c₂)) hpair
  have h11 := conv_sum_translated f g r₁ c₁ s hcov1
  have h12 := conv_sum_translated f g r₁ c₂ s hcov2
  have h21 := conv_sum_translated f g r₂ c₁ s hcov1
  have h22 := conv_sum_translated f g r₂ c₂ s hcov2
  change 0 ≤ finiteConv f g (r₁-c₁)*finiteConv f g (r₂-c₂) -
    finiteConv f g (r₁-c₂)*finiteConv f g (r₂-c₁)
  rw [h11,h22,h12,h21]
  dsimp only at hCB
  nlinarith

/-- In particular, every adjacent Turán inequality survives a finite
convolution of TP2 sequences. -/
theorem finiteConv_turan (f : ℤ → ℝ) (g : ℤ →₀ ℝ)
    (hf : ToeplitzTP2 f)
    (hg : ToeplitzTP2 (fun i : ℤ => g i)) :
    Turan (finiteConv f g) := by
  intro n
  have h := finiteConv_toeplitzTP2 f g hf hg n (n+1) 0 1 (by omega) (by omega)
  have h0 : n+1-1=n := by omega
  have h1 : n-0=n := by omega
  have h2 : n+1-0=n+1 := by omega
  rw [h0, h1, h2] at h
  nlinarith

/-- Toeplitz TP2 itself forces gapless positive support. -/
theorem toeplitzTP2_gapless (f : ℤ → ℝ)
    (hf : ToeplitzTP2 f) (hnon : Nonnegative f) : Gapless f := by
  intro a b c hab hbc ha hc
  have h := hf a b (b-c) 0 hab (by omega)
  have hidx1 : a-(b-c)=a+c-b := by omega
  have hidx2 : b-(b-c)=c := by omega
  rw [hidx1, hidx2, sub_zero, sub_zero] at h
  by_contra hnot
  have hbzero : f b = 0 := le_antisymm (le_of_not_gt hnot) (hnon b)
  rw [hbzero] at h
  nlinarith

/-- Every coefficient of a convolution of nonnegative sequences is
nonnegative. -/
theorem finiteConv_nonnegative (f : ℤ → ℝ) (g : ℤ →₀ ℝ)
    (hf : Nonnegative f) (hg : Nonnegative (fun i : ℤ => g i)) :
    Nonnegative (finiteConv f g) := by
  intro n
  unfold finiteConv
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hf _) (hg _))

/-- Finite nonnegative convolution preserves log-concavity and gapless
support. The gapless premise is essential: local Turán inequalities alone
allow separated positive islands. -/
theorem finite_nonnegative_convolution_logconcave (f : ℤ → ℝ) (g : ℤ →₀ ℝ)
    (hfnon : Nonnegative f) (hft : Turan f) (hfgap : Gapless f)
    (hgnon : Nonnegative (fun i : ℤ => g i))
    (hgt : Turan (fun i : ℤ => g i))
    (hggap : Gapless (fun i : ℤ => g i)) :
    Nonnegative (finiteConv f g) ∧
      Turan (finiteConv f g) ∧ Gapless (finiteConv f g) := by
  have hft2 := toeplitzTP2_of_turan f hfnon hft hfgap
  have hgt2 := toeplitzTP2_of_turan (fun i : ℤ => g i) hgnon hgt hggap
  have hct2 := finiteConv_toeplitzTP2 f g hft2 hgt2
  have hcnon := finiteConv_nonnegative f g hfnon hgnon
  exact ⟨hcnon, finiteConv_turan f g hft2 hgt2,
    toeplitzTP2_gapless (finiteConv f g) hct2 hcnon⟩

/-- Identify the finite convolution with multiplication in the genuine
Laurent-polynomial ring. This is the native finite-support algebra that
also contains ordinary polynomial products via `Polynomial.toLaurent`. -/
theorem finiteConv_eq_addMonoidAlgebra_mul (p q : AddMonoidAlgebra ℝ ℤ)
    (n : ℤ) :
    finiteConv (fun i => p i) q n = (p*q) n := by
  classical
  rw [AddMonoidAlgebra.mul_apply_right]
  rfl

/-- The TP2 convolution result is already a genuine coefficient-product
theorem for all finitely supported Laurent polynomials, not just a proxy
sequence with a chosen summation bound. -/
theorem addMonoidAlgebra_mul_toeplitzTP2 (p q : AddMonoidAlgebra ℝ ℤ)
    (hp : ToeplitzTP2 (fun i : ℤ => p i))
    (hq : ToeplitzTP2 (fun i : ℤ => q i)) :
    ToeplitzTP2 (fun i : ℤ => (p*q) i) := by
  have h := finiteConv_toeplitzTP2 (fun i : ℤ => p i) q hp hq
  have heq : finiteConv (fun i : ℤ => p i) q = fun i : ℤ => (p*q) i := by
    funext i
    exact finiteConv_eq_addMonoidAlgebra_mul p q i
  simpa only [heq] using h

/-- Native real-polynomial multiplication preserves all Toeplitz minors
after the standard semiring embedding into Laurent polynomials. -/
theorem realPolynomial_mul_toeplitzTP2 (p q : Polynomial ℝ)
    (hp : ToeplitzTP2 (fun i : ℤ => (Polynomial.toLaurent p) i))
    (hq : ToeplitzTP2 (fun i : ℤ => (Polynomial.toLaurent q) i)) :
    ToeplitzTP2 (fun i : ℤ => (Polynomial.toLaurent (p*q)) i) := by
  simpa only [map_mul] using
    (addMonoidAlgebra_mul_toeplitzTP2 (Polynomial.toLaurent p)
      (Polynomial.toLaurent q) hp hq)

/-- Exact agreement of genuine polynomial coefficients with their
Laurent embedding at every nonnegative exponent. -/
theorem toLaurent_nat_coeff (p : Polynomial ℝ) (j : ℕ) :
    (Polynomial.toLaurent p) (j : ℤ) = p.coeff j := by
  rw [Polynomial.toLaurent_apply]
  exact Finsupp.mapDomain_apply (by exact_mod_cast Nat.cast_injective) _ _

/-- Genuine polynomial coefficients vanish at every negative exponent
in the Laurent embedding. -/
theorem toLaurent_neg_coeff (p : Polynomial ℝ) (j : ℤ) (hj : j < 0) :
    (Polynomial.toLaurent p) j = 0 := by
  rw [Polynomial.toLaurent_apply]
  apply Finsupp.mapDomain_notin_range
  intro ⟨k, hk⟩
  have hnon : 0 ≤ j := by rw [←hk]; exact Int.natCast_nonneg _
  omega

/-- A polynomial with nonnegative real coefficients has nonnegative
Laurent coefficient sequence on the entire integer line. -/
theorem toLaurent_nonnegative (p : Polynomial ℝ)
    (hp : ∀ j : ℕ, 0 ≤ p.coeff j) :
    Nonnegative (fun i : ℤ => (Polynomial.toLaurent p) i) := by
  intro i
  change 0 ≤ (Polynomial.toLaurent p) i
  by_cases hi : i < 0
  · rw [toLaurent_neg_coeff p i hi]
  · have hi0 : 0 ≤ i := by omega
    have hieq : (i.toNat:ℤ)=i := Int.toNat_of_nonneg hi0
    rw [←hieq, toLaurent_nat_coeff]
    exact hp _

/-- Ordinary finite polynomial Turán inequalities, including the leading
and trailing boundary where one coefficient may vanish. -/
def PolynomialTuran (p : Polynomial ℝ) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    p.coeff (j-1)*p.coeff (j+1) ≤ (p.coeff j)^2

def PolynomialGapless (p : Polynomial ℝ) : Prop :=
  ∀ a b c : ℕ, a < b → b < c →
    0 < p.coeff a → 0 < p.coeff c → 0 < p.coeff b

/-- Transfer every genuine Nat-index Turán inequality to the integer
coefficient line used by the Toeplitz convolution theorem. -/
theorem toLaurent_turan (p : Polynomial ℝ)
    (hp : PolynomialTuran p) :
    Turan (fun i : ℤ => (Polynomial.toLaurent p) i) := by
  intro i
  change (Polynomial.toLaurent p) (i-1) *
    (Polynomial.toLaurent p) (i+1) ≤ ((Polynomial.toLaurent p) i)^2
  by_cases hi : 0 < i
  · let j : ℕ := i.toNat
    have hcast : (j : ℤ) = i := Int.toNat_of_nonneg (by omega)
    have hj : 1 ≤ j := by omega
    have hprev : ((j-1:ℕ):ℤ)=i-1 := by omega
    have hnext : ((j+1:ℕ):ℤ)=i+1 := by omega
    rw [←hprev, ←hnext, ←hcast]
    simp only [toLaurent_nat_coeff]
    exact hp j hj
  · have hiNeg : i-1 < 0 := by omega
    rw [toLaurent_neg_coeff p (i-1) hiNeg, zero_mul]
    exact sq_nonneg _

/-- Transfer absence of internal positive-support holes from genuine
polynomial coefficients to its zero-extended Laurent coefficient line. -/
theorem toLaurent_gapless (p : Polynomial ℝ)
    (hp : PolynomialGapless p) :
    Gapless (fun i : ℤ => (Polynomial.toLaurent p) i) := by
  intro a b c hab hbc ha hc
  change 0 < (Polynomial.toLaurent p) a at ha
  change 0 < (Polynomial.toLaurent p) c at hc
  change 0 < (Polynomial.toLaurent p) b
  have ha0 : 0 ≤ a := by
    by_contra hn
    have hh : a < 0 := by omega
    rw [toLaurent_neg_coeff p a hh] at ha
    norm_num at ha
  have hb0 : 0 ≤ b := by omega
  have hc0 : 0 ≤ c := by omega
  have ha' : (a.toNat:ℤ) = a := Int.toNat_of_nonneg ha0
  have hb' : (b.toNat:ℤ) = b := Int.toNat_of_nonneg hb0
  have hc' : (c.toNat:ℤ) = c := Int.toNat_of_nonneg hc0
  have hnatab : a.toNat < b.toNat := by omega
  have hnatbc : b.toNat < c.toNat := by omega
  rw [←ha', toLaurent_nat_coeff] at ha
  rw [←hc', toLaurent_nat_coeff] at hc
  rw [←hb', toLaurent_nat_coeff]
  exact hp a.toNat b.toNat c.toNat hnatab hnatbc ha hc

/-- A fully native polynomial-product version of finite log-concavity
preservation. Repeated silent-fiber products use this exact statement. -/
theorem realPolynomial_mul_turan (p q : Polynomial ℝ)
    (hpn : ∀ j : ℕ, 0 ≤ p.coeff j)
    (hpt : PolynomialTuran p) (hpg : PolynomialGapless p)
    (hqn : ∀ j : ℕ, 0 ≤ q.coeff j)
    (hqt : PolynomialTuran q) (hqg : PolynomialGapless q) :
    PolynomialTuran (p*q) := by
  have hP : ToeplitzTP2 (fun i : ℤ => (Polynomial.toLaurent p) i) :=
    toeplitzTP2_of_turan _ (toLaurent_nonnegative p hpn)
      (toLaurent_turan p hpt) (toLaurent_gapless p hpg)
  have hQ : ToeplitzTP2 (fun i : ℤ => (Polynomial.toLaurent q) i) :=
    toeplitzTP2_of_turan _ (toLaurent_nonnegative q hqn)
      (toLaurent_turan q hqt) (toLaurent_gapless q hqg)
  have hPQ := realPolynomial_mul_toeplitzTP2 p q hP hQ
  intro j hj
  have h := hPQ (j:ℤ) ((j:ℤ)+1) 0 1 (by omega) (by omega)
  have hidx : ((j:ℤ)+1)-1=(j:ℤ) := by omega
  have hidx2 : ((j:ℤ)+1)-0=((j+1:ℕ):ℤ) := by omega
  have hidx3 : (j:ℤ)-1=((j-1:ℕ):ℤ) := by omega
  simp only [sub_zero, hidx, hidx2, hidx3, toLaurent_nat_coeff] at h
  nlinarith

theorem polynomial_real_mul_nonnegative_logconcave_gapless
    (p q : Polynomial ℝ)
    (hpn : ∀ j : ℕ, 0 ≤ p.coeff j)
    (hpt : PolynomialTuran p) (hpg : PolynomialGapless p)
    (hqn : ∀ j : ℕ, 0 ≤ q.coeff j)
    (hqt : PolynomialTuran q) (hqg : PolynomialGapless q) :
    (∀ j : ℕ, 0 ≤ (p*q).coeff j) ∧
      PolynomialTuran (p*q) ∧ PolynomialGapless (p*q) := by
  let P := Polynomial.toLaurent p
  let Q := Polynomial.toLaurent q
  have hconv := finite_nonnegative_convolution_logconcave
    (fun i : ℤ => P i) Q
    (toLaurent_nonnegative p hpn) (toLaurent_turan p hpt) (toLaurent_gapless p hpg)
    (toLaurent_nonnegative q hqn) (toLaurent_turan q hqt) (toLaurent_gapless q hqg)
  have hcoe (i : ℤ) :
      finiteConv (fun k : ℤ => P k) Q i = (Polynomial.toLaurent (p*q)) i := by
    rw [finiteConv_eq_addMonoidAlgebra_mul]
    exact congrArg (fun h : AddMonoidAlgebra ℝ ℤ => h i) (by simp [P, Q])
  have hnon : ∀ j : ℕ, 0 ≤ (p*q).coeff j := by
    intro j
    have hj := hconv.1 (j : ℤ)
    rw [hcoe, toLaurent_nat_coeff] at hj
    exact hj
  have htur : PolynomialTuran (p*q) :=
    realPolynomial_mul_turan p q hpn hpt hpg hqn hqt hqg
  have hgap : PolynomialGapless (p*q) := by
    intro a b c hab hbc ha hc
    have ha' : 0 < finiteConv (fun k : ℤ => P k) Q (a : ℤ) := by
      rw [hcoe, toLaurent_nat_coeff]
      exact ha
    have hc' : 0 < finiteConv (fun k : ℤ => P k) Q (c : ℤ) := by
      rw [hcoe, toLaurent_nat_coeff]
      exact hc
    have hb := hconv.2.2 (a : ℤ) (b : ℤ) (c : ℤ)
      (by exact_mod_cast hab) (by exact_mod_cast hbc) ha' hc'
    rw [hcoe, toLaurent_nat_coeff] at hb
    exact hb
  exact ⟨hnon, htur, hgap⟩

private theorem tail_antitone_of_drop
    (a : ℕ → ℝ)
    (hnon : ∀ k, 0 ≤ a k)
    (hlc : ∀ k, a k * a (k + 2) ≤ (a (k + 1)) ^ 2)
    (hgap : ∀ i j k : ℕ, i < j → j < k → 0 < a i → 0 < a k → 0 < a j)
    (m : ℕ) (hdrop : a (m + 1) < a m) :
    ∀ k ≥ m, a (k + 1) ≤ a k := by
  have hpos_m : 0 < a m := by have := hnon (m+1); linarith
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hdrop.le
  | succ k hk ih =>
    by_cases hz : a (k+1) = 0
    · have hz2 : a (k+2) = 0 := by
        by_contra hne
        have hpositive : 0 < a (k+2) := by
          have hn := hnon (k+2)
          rcases lt_or_eq_of_le hn with h | h
          · exact h
          · exact False.elim (hne h.symm)
        have hneed := hgap m (k+1) (k+2) (by omega) (by omega) hpos_m hpositive
        exact (ne_of_gt hneed) hz
      simp [hz, hz2]
    · have hpositive : 0 < a (k+1) := by
        have hn := hnon (k+1)
        rcases lt_or_eq_of_le hn with h | h
        · exact h
        · exact False.elim (hz h.symm)
      have hx : 0 < a k := lt_of_lt_of_le hpositive ih
      have hsq : (a (k+1)) ^ 2 ≤ a k * a (k+1) := by
        have hmul := mul_nonneg (sub_nonneg.mpr ih) (le_of_lt hpositive)
        nlinarith
      have htur := hlc k
      by_contra hnot
      have hbad : 0 < a (k+2) - a (k+1) := by linarith
      have hprod := mul_pos hx hbad
      nlinarith

theorem polynomial_logconcave_gapless_unimodal
    (p : Polynomial ℝ)
    (hnon : ∀ j : ℕ, 0 ≤ p.coeff j)
    (hlc : PolynomialTuran p)
    (hgap : PolynomialGapless p) :
    ∃ m : ℕ, (∀ k < m, p.coeff k ≤ p.coeff (k+1)) ∧
      (∀ k ≥ m, p.coeff (k+1) ≤ p.coeff k) := by
  have htur : ∀ j : ℕ,
      p.coeff j * p.coeff (j+2) ≤ (p.coeff (j+1)) ^ 2 := by
    intro j
    simpa [Nat.add_sub_cancel_left] using hlc (j+1) (by omega)
  classical
  by_cases hdescent : ∃ k : ℕ, p.coeff (k+1) < p.coeff k
  · let m := Nat.find hdescent
    have hm : p.coeff (m+1) < p.coeff m := Nat.find_spec hdescent
    refine ⟨m, ?_, ?_⟩
    · intro k hk
      by_contra hnot
      exact (Nat.find_min hdescent hk) (lt_of_not_ge hnot)
    · exact tail_antitone_of_drop
        (fun k => p.coeff k) hnon htur hgap m hm
  · refine ⟨p.natDegree+1, ?_, ?_⟩
    · intro k hk
      by_contra hnot
      exact hdescent ⟨k, lt_of_not_ge hnot⟩
    · intro k hk
      have h0 : p.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have h1 : p.coeff (k+1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [h0, h1]

end LogConcaveProduct
