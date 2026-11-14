import Mathlib

open scoped BigOperators

namespace GapThreeGraphConnectionAudit

/-- Closed-neighborhood domination on a finite vertex type α. -/
def IsDominating {α : Type*} (adj : α → α → Prop) (S : Finset α) : Prop :=
  ∀ v : α, v ∈ S ∨ ∃ u ∈ S, adj v u

/-- The k-rank dominating set family D_k(G) on a finite vertex type α. -/
def domRank {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (k : ℕ) : Finset (Finset α) :=
  Finset.univ.filter (fun S => S.card = k ∧ IsDominating adj S)

/-- Deletion-critical dominating vertices C(S) = a(S). -/
def domCritical {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (S : Finset α) : Finset α :=
  S.filter (fun x => ¬ IsDominating adj (S.erase x))

/-- Removable dominating vertices S \ C(S). -/
def domRemovable {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (S : Finset α) : Finset α :=
  S.filter (fun x => IsDominating adj (S.erase x))

private lemma isDominating_upward {α : Type*} (adj : α → α → Prop)
    {S U : Finset α} (hSU : S ⊆ U) (hS : IsDominating adj S) :
    IsDominating adj U := by
  intro v
  rcases hS v with hvS | ⟨u, huS, hadj⟩
  · exact Or.inl (hSU hvS)
  · exact Or.inr ⟨u, hSU huS, hadj⟩

private lemma domCritical_card_le {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    {S U : Finset α} (hS : IsDominating adj S) (hSU : S ⊆ U) :
    (domCritical adj U).card ≤ (domCritical adj S).card := by
  apply Finset.card_le_card
  intro x hx
  rw [domCritical, Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxU, hxUdel⟩
  refine ⟨?_, ?_⟩
  · by_contra hxS
    apply hxUdel
    apply isDominating_upward adj _ hS
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun hyx => hxS (hyx ▸ hy), hSU hy⟩
  · intro hSdel
    apply hxUdel
    exact isDominating_upward adj (Finset.erase_subset_erase x hSU) hSdel

private def lowerInc {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (j : ℕ) :
    Finset (Σ _ : Finset α, α) :=
  (domRank adj (j - 1)).sigma (fun S => Finset.univ \ S)

private def upperInc {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (j : ℕ) :
    Finset (Σ _ : Finset α, α) :=
  (domRank adj j).sigma (fun U => domRemovable adj U)

private lemma sum_domRemovable_eq {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (j : ℕ) (hj : 1 ≤ j) :
    ∑ U ∈ domRank adj j, (domRemovable adj U).card =
      (Fintype.card α - (j - 1)) * (domRank adj (j - 1)).card := by
  have h_low : (lowerInc adj j).card =
      (Fintype.card α - (j - 1)) * (domRank adj (j - 1)).card := by
    rw [lowerInc, Finset.card_sigma]
    have h_congr : ∑ S ∈ domRank adj (j - 1), (Finset.univ \ S).card =
        ∑ _S ∈ domRank adj (j - 1), (Fintype.card α - (j - 1)) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [domRank, Finset.mem_filter] at hS
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hS.2.1]
    rw [h_congr, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
  have h_up : (upperInc adj j).card =
      ∑ U ∈ domRank adj j, (domRemovable adj U).card := by
    rw [upperInc, Finset.card_sigma]
  rw [← h_up, ← h_low]
  symm
  apply Finset.card_bij (fun p _ => ⟨insert p.2 p.1, p.2⟩)
  · rintro ⟨S, x⟩ hp
    rw [lowerInc, Finset.mem_sigma, domRank, Finset.mem_filter, Finset.mem_sdiff] at hp
    rcases hp with ⟨⟨_, hScard, hPS⟩, ⟨_, hxS⟩⟩
    rw [upperInc, Finset.mem_sigma, domRank, Finset.mem_filter,
        domRemovable, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ⟨Finset.mem_insert_self x S, ?_⟩⟩
    · rw [Finset.card_insert_of_notMem hxS, hScard]
      omega
    · exact isDominating_upward adj (Finset.subset_insert x S) hPS
    · rw [Finset.erase_insert hxS]
      exact hPS
  · rintro ⟨S1, x1⟩ hp1 ⟨S2, x2⟩ hp2 heq
    rw [lowerInc, Finset.mem_sigma, Finset.mem_sdiff] at hp1 hp2
    dsimp at hp1 hp2 heq
    injection heq with hU hx
    subst hx
    have h1 := Finset.erase_insert hp1.2.2
    have h2 := Finset.erase_insert hp2.2.2
    have hS : S1 = S2 := by rw [← h1, ← h2, hU]
    subst hS
    rfl
  · rintro ⟨U, x⟩ hq
    rw [upperInc, Finset.mem_sigma, domRank, Finset.mem_filter,
        domRemovable, Finset.mem_filter] at hq
    rcases hq with ⟨⟨_, hUcard, _⟩, ⟨hxU, hPdel⟩⟩
    refine ⟨⟨U.erase x, x⟩, ?_, ?_⟩
    · rw [lowerInc, Finset.mem_sigma, domRank, Finset.mem_filter, Finset.mem_sdiff]
      refine ⟨⟨Finset.mem_univ _, ?_, hPdel⟩, ⟨Finset.mem_univ _, Finset.notMem_erase x U⟩⟩
      rw [Finset.card_erase_of_mem hxU, hUcard]
    · simp [Finset.insert_erase hxU]

/-- 1. Unconditional graph-level proof of Beaton-Schoonhoven Lemma 3. -/
private theorem graph_domination_lemma3_identity {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (j : ℕ) (hj : 1 ≤ j) :
    (∑ U ∈ domRank adj j, (domCritical adj U).card) +
      (Fintype.card α - (j - 1)) * (domRank adj (j - 1)).card =
      (domRank adj j).card * j := by
  have h_part : ∑ U ∈ domRank adj j, ((domRemovable adj U).card + (domCritical adj U).card) =
      ∑ _U ∈ domRank adj j, j := by
    apply Finset.sum_congr rfl
    intro U hU
    rw [domRank, Finset.mem_filter] at hU
    have h_add : (domRemovable adj U).card + (domCritical adj U).card = U.card := by
      simpa [domRemovable, domCritical] using
        Finset.card_filter_add_card_filter_not (s := U) (p := fun x => IsDominating adj (U.erase x))
    rw [h_add, hU.2.1]
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, sum_domRemovable_eq adj j hj] at h_part
  omega

/-- 2. Unconditional graph-level weighted incidence critical-sum inequality. -/
private theorem graph_domination_weighted_incidence_le {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (j : ℕ) (hj : 1 ≤ j) :
    ∑ U ∈ domRank adj j, (domRemovable adj U).card * (domCritical adj U).card ≤
      (Fintype.card α - (j - 1)) * ∑ S ∈ domRank adj (j - 1), (domCritical adj S).card := by
  have h_low_sum : ∑ p ∈ lowerInc adj j, (domCritical adj p.1).card =
      (Fintype.card α - (j - 1)) * ∑ S ∈ domRank adj (j - 1), (domCritical adj S).card := by
    rw [lowerInc, Finset.sum_sigma]
    have h_congr : ∑ S ∈ domRank adj (j - 1), ∑ _x ∈ Finset.univ \ S, (domCritical adj S).card =
        ∑ S ∈ domRank adj (j - 1), (Fintype.card α - (j - 1)) * (domCritical adj S).card := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [domRank, Finset.mem_filter] at hS
      dsimp
      rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_sdiff, Finset.inter_univ,
          Finset.card_univ, hS.2.1]
    rw [h_congr, ← Finset.mul_sum]
  have h_up_sum : ∑ p ∈ upperInc adj j, (domCritical adj p.1).card =
      ∑ U ∈ domRank adj j, (domRemovable adj U).card * (domCritical adj U).card := by
    rw [upperInc, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro U _
    dsimp
    rw [Finset.sum_const, Nat.nsmul_eq_mul]
  rw [← h_up_sum, ← h_low_sum]
  have h_bij : ∑ p ∈ upperInc adj j, (domCritical adj p.1).card =
      ∑ p ∈ lowerInc adj j, (domCritical adj (insert p.2 p.1)).card := by
    symm
    apply Finset.sum_bij (fun p _ => ⟨insert p.2 p.1, p.2⟩)
    · rintro ⟨S, x⟩ hp
      rw [lowerInc, Finset.mem_sigma, domRank, Finset.mem_filter, Finset.mem_sdiff] at hp
      rcases hp with ⟨⟨_, hScard, hPS⟩, ⟨_, hxS⟩⟩
      rw [upperInc, Finset.mem_sigma, domRank, Finset.mem_filter,
          domRemovable, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ⟨Finset.mem_insert_self x S, ?_⟩⟩
      · rw [Finset.card_insert_of_notMem hxS, hScard]
        omega
      · exact isDominating_upward adj (Finset.subset_insert x S) hPS
      · rw [Finset.erase_insert hxS]
        exact hPS
    · rintro ⟨S1, x1⟩ hp1 ⟨S2, x2⟩ hp2 heq
      rw [lowerInc, Finset.mem_sigma, Finset.mem_sdiff] at hp1 hp2
      dsimp at hp1 hp2 heq
      injection heq with hU hx
      subst hx
      have h1 := Finset.erase_insert hp1.2.2
      have h2 := Finset.erase_insert hp2.2.2
      have hS : S1 = S2 := by rw [← h1, ← h2, hU]
      subst hS
      rfl
    · rintro ⟨U, x⟩ hq
      rw [upperInc, Finset.mem_sigma, domRank, Finset.mem_filter,
          domRemovable, Finset.mem_filter] at hq
      rcases hq with ⟨⟨_, hUcard, _⟩, ⟨hxU, hPdel⟩⟩
      refine ⟨⟨U.erase x, x⟩, ?_, ?_⟩
      · rw [lowerInc, Finset.mem_sigma, domRank, Finset.mem_filter, Finset.mem_sdiff]
        refine ⟨⟨Finset.mem_univ _, ?_, hPdel⟩, ⟨Finset.mem_univ _, Finset.notMem_erase x U⟩⟩
        rw [Finset.card_erase_of_mem hxU, hUcard]
      · simp [Finset.insert_erase hxU]
    · rintro ⟨S, x⟩ _
      rfl
  rw [h_bij]
  apply Finset.sum_le_sum
  rintro ⟨S, x⟩ hp
  rw [lowerInc, Finset.mem_sigma, domRank, Finset.mem_filter] at hp
  exact domCritical_card_le adj hp.1.2.2 (Finset.subset_insert x S)

/-- d_k(G) as a real number. -/
noncomputable def dR {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (k : ℕ) : ℝ :=
  ((domRank adj k).card : ℝ)

/-- a(G, k): total number of critical vertices over all dominating k-sets. -/
noncomputable def critSum {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (k : ℕ) : ℝ :=
  ∑ U ∈ domRank adj k, ((domCritical adj U).card : ℝ)

/-- c_k: mean critical count over dominating k-sets. -/
noncomputable def critMean {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (k : ℕ) : ℝ :=
  critSum adj k / dR adj k

/-- v_k: population variance of the critical count over dominating k-sets. -/
noncomputable def critVar {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (k : ℕ) : ℝ :=
  (∑ U ∈ domRank adj k, (((domCritical adj U).card : ℝ) - critMean adj k) ^ 2) / dR adj k

private lemma bridge_lemma3 {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (i : ℕ) (hi : i + 1 ≤ Fintype.card α) :
    critSum adj (i + 1) + ((Fintype.card α : ℝ) - i) * dR adj i =
      dR adj (i + 1) * ((i : ℝ) + 1) := by
  have h := graph_domination_lemma3_identity adj (i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  have hle : i ≤ Fintype.card α := by omega
  have hR := congrArg (fun x : ℕ => (x : ℝ)) h
  simp only at hR
  push_cast [Nat.cast_sub hle] at hR
  simp only [critSum, dR]
  linarith

private lemma bridge_weighted {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (i : ℕ) (hi : i + 1 ≤ Fintype.card α) :
    ∑ U ∈ domRank adj (i + 1),
        (((i : ℝ) + 1) - ((domCritical adj U).card : ℝ)) * ((domCritical adj U).card : ℝ)
      ≤ ((Fintype.card α : ℝ) - i) * critSum adj i := by
  have h := graph_domination_weighted_incidence_le adj (i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h
  have hle : i ≤ Fintype.card α := by omega
  have hR : ((∑ U ∈ domRank adj (i + 1), (domRemovable adj U).card * (domCritical adj U).card : ℕ) : ℝ) ≤
      (((Fintype.card α - i) * ∑ S ∈ domRank adj i, (domCritical adj S).card : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast [Nat.cast_sub hle] at hR
  have h_rw : ∀ U ∈ domRank adj (i + 1),
      ((domRemovable adj U).card : ℝ) * ((domCritical adj U).card : ℝ) =
      (((i : ℝ) + 1) - ((domCritical adj U).card : ℝ)) * ((domCritical adj U).card : ℝ) := by
    intro U hU
    rw [domRank, Finset.mem_filter] at hU
    have h_add : (domRemovable adj U).card + (domCritical adj U).card = U.card := by
      simpa [domRemovable, domCritical] using
        Finset.card_filter_add_card_filter_not (s := U) (p := fun x => IsDominating adj (U.erase x))
    have h_add' : ((domRemovable adj U).card : ℝ) + ((domCritical adj U).card : ℝ) =
        (i : ℝ) + 1 := by
      have h2 := congrArg (fun x : ℕ => (x : ℝ)) h_add
      simp only at h2
      push_cast at h2
      rw [h2]
      simp [hU.2.1]
    have h3 : ((domRemovable adj U).card : ℝ) = ((i : ℝ) + 1) - ((domCritical adj U).card : ℝ) := by
      linarith
    rw [h3]
  rw [Finset.sum_congr rfl h_rw] at hR
  simp only [critSum]
  exact hR

private lemma sum_eq_d_mul_mean {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (k : ℕ) (hd : 0 < dR adj k) :
    critSum adj k = dR adj k * critMean adj k := by
  have hne : dR adj k ≠ 0 := ne_of_gt hd
  unfold critMean
  field_simp

private lemma vsum_eq_d_mul_var {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (k : ℕ) (hd : 0 < dR adj k) :
    ∑ U ∈ domRank adj k, (((domCritical adj U).card : ℝ) - critMean adj k) ^ 2 =
      dR adj k * critVar adj k := by
  have hne : dR adj k ≠ 0 := ne_of_gt hd
  unfold critVar
  field_simp

/-- Graph-level incidence-variance inequality (no tree hypothesis, no abstract-family premise):
for every finite graph and every rank i with i + 1 ≤ n and d_i, d_{i+1} > 0,
(i + 1 - c_{i+1}) (c_{i+1} - c_i) ≤ v_{i+1}. -/
theorem graph_incidence_variance_inequality {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (i : ℕ) (hi : i + 1 ≤ Fintype.card α)
    (hd_i : 0 < dR adj i) (hd_j : 0 < dR adj (i + 1)) :
    (((i : ℝ) + 1) - critMean adj (i + 1)) * (critMean adj (i + 1) - critMean adj i) ≤
      critVar adj (i + 1) := by
  have hSj := sum_eq_d_mul_mean adj (i + 1) hd_j
  have hSi := sum_eq_d_mul_mean adj i hd_i
  have hV := vsum_eq_d_mul_var adj (i + 1) hd_j
  have h3 := bridge_lemma3 adj i hi
  have hW := bridge_weighted adj i hi
  have hcard : ((domRank adj (i + 1)).card : ℝ) = dR adj (i + 1) := rfl
  have h_mean : ∑ U ∈ domRank adj (i + 1), ((domCritical adj U).card : ℝ) =
      dR adj (i + 1) * critMean adj (i + 1) := by
    rw [← hSj]; rfl
  have h_pt : ∀ U ∈ domRank adj (i + 1),
      (((i : ℝ) + 1) - ((domCritical adj U).card : ℝ)) * ((domCritical adj U).card : ℝ) =
        (((i : ℝ) + 1) - 2 * critMean adj (i + 1)) * ((domCritical adj U).card : ℝ) +
          critMean adj (i + 1) ^ 2 -
          (((domCritical adj U).card : ℝ) - critMean adj (i + 1)) ^ 2 := by
    intro U _
    ring
  have h_upper : ∑ U ∈ domRank adj (i + 1),
      (((i : ℝ) + 1) - ((domCritical adj U).card : ℝ)) * ((domCritical adj U).card : ℝ) =
      (((i : ℝ) + 1) - 2 * critMean adj (i + 1)) * (dR adj (i + 1) * critMean adj (i + 1)) +
        dR adj (i + 1) * critMean adj (i + 1) ^ 2 - dR adj (i + 1) * critVar adj (i + 1) := by
    rw [Finset.sum_congr rfl h_pt, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, h_mean, hcard, hV]
  have h_lin : ((Fintype.card α : ℝ) - i) * dR adj i =
      dR adj (i + 1) * ((i : ℝ) + 1) - dR adj (i + 1) * critMean adj (i + 1) := by
    rw [hSj] at h3; linarith
  have h_rhs : ((Fintype.card α : ℝ) - i) * critSum adj i =
      dR adj (i + 1) * (((i : ℝ) + 1) - critMean adj (i + 1)) * critMean adj i := by
    rw [hSi]
    calc ((Fintype.card α : ℝ) - i) * (dR adj i * critMean adj i)
        = (((Fintype.card α : ℝ) - i) * dR adj i) * critMean adj i := by ring
      _ = (dR adj (i + 1) * ((i : ℝ) + 1) - dR adj (i + 1) * critMean adj (i + 1)) *
            critMean adj i := by rw [h_lin]
      _ = dR adj (i + 1) * (((i : ℝ) + 1) - critMean adj (i + 1)) * critMean adj i := by ring
  have h_main : dR adj (i + 1) *
      ((((i : ℝ) + 1) - critMean adj (i + 1)) * (critMean adj (i + 1) - critMean adj i)) ≤
      dR adj (i + 1) * critVar adj (i + 1) := by
    have := hW
    rw [h_upper, h_rhs] at this
    nlinarith
  exact le_of_mul_le_mul_left h_main hd_j

/-- Graph-level central-window theorem at gap Γ - γ = 3. The only inputs not derived here are
the two monotone tails (Beaton-Schoonhoven Theorems 6 and 16), positivity of d_{A+1}, d_{A+2},
the rank cutoff γ + 4 ≤ A + 2 ≤ n, and the pointwise critical bounds
2γ - j ≤ |a(U)| ≤ 2γ + 6 - j at j = A + 2 (Lemmas 5 and 15 with Γ = γ + 3).
Conclusion: c_{A+2} - c_{A+1} ≤ 2, no strict valley at A + 1, and weak unimodality of d_k(G). -/
theorem graph_central_window_weak_unimodal {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (A : ℕ) (γ : ℝ)
    (h_left : ∀ k < A, dR adj k ≤ dR adj (k + 1))
    (h_right : ∀ k ≥ A + 2, dR adj (k + 1) ≤ dR adj k)
    (hd_i : 0 < dR adj (A + 1)) (hd_j : 0 < dR adj (A + 2))
    (h_jn : A + 2 ≤ Fintype.card α)
    (h_gap : γ + 4 ≤ (A : ℝ) + 2)
    (h_bounds : ∀ U ∈ domRank adj (A + 2),
      2 * γ - ((A : ℝ) + 2) ≤ ((domCritical adj U).card : ℝ) ∧
      ((domCritical adj U).card : ℝ) ≤ 2 * γ - ((A : ℝ) + 2) + 6) :
    critMean adj (A + 2) - critMean adj (A + 1) ≤ 2 ∧
      ¬ (dR adj (A + 1) < dR adj A ∧ dR adj (A + 1) < dR adj (A + 2)) ∧
      ∃ m : ℕ, (∀ k < m, dR adj k ≤ dR adj (k + 1)) ∧ (∀ k ≥ m, dR adj (k + 1) ≤ dR adj k) := by
  have e : A + 1 + 1 = A + 2 := by omega
  have hd_j' : 0 < dR adj (A + 1 + 1) := by rw [e]; exact hd_j
  have hIV := graph_incidence_variance_inequality adj (A + 1) (by omega) hd_i hd_j'
  rw [e] at hIV
  have hcast : ((A + 1 : ℕ) : ℝ) + 1 = (A : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hIV
  have h3j := bridge_lemma3 adj (A + 1) (by omega)
  rw [e] at h3j
  have hcast2 : ((A + 1 : ℕ) : ℝ) = (A : ℝ) + 1 := by push_cast; ring
  rw [hcast2] at h3j
  have h3i := bridge_lemma3 adj A (by omega)
  have hSj := sum_eq_d_mul_mean adj (A + 2) hd_j
  have hSi := sum_eq_d_mul_mean adj (A + 1) hd_i
  have hV := vsum_eq_d_mul_var adj (A + 2) hd_j
  rw [hSj] at h3j
  rw [hSi] at h3i
  have hcard : ((domRank adj (A + 2)).card : ℝ) = dR adj (A + 2) := rfl
  have h_mean : ∑ U ∈ domRank adj (A + 2), ((domCritical adj U).card : ℝ) =
      dR adj (A + 2) * critMean adj (A + 2) := by
    rw [← hSj]; rfl
  set L : ℝ := 2 * γ - ((A : ℝ) + 2) with hL
  set cj : ℝ := critMean adj (A + 2) with hcj
  set ci : ℝ := critMean adj (A + 1) with hci
  set dj : ℝ := dR adj (A + 2) with hdj
  set di : ℝ := dR adj (A + 1) with hdi
  -- mean bounds from pointwise bounds
  have h_lo : dj * L ≤ dj * cj := by
    have hs := Finset.sum_le_sum (fun U hU => (h_bounds U hU).1)
    rw [Finset.sum_const, nsmul_eq_mul, hcard, h_mean] at hs
    linarith
  have h_hi : dj * cj ≤ dj * (L + 6) := by
    have hs := Finset.sum_le_sum (fun U hU => (h_bounds U hU).2)
    rw [Finset.sum_const, nsmul_eq_mul, hcard, h_mean] at hs
    linarith
  have hc_L : L ≤ cj := le_of_mul_le_mul_left h_lo hd_j
  have hc_U : cj ≤ L + 6 := le_of_mul_le_mul_left h_hi hd_j
  -- Bhatia-Davis on the graph rank A + 2
  have h_bd : dj * critVar adj (A + 2) ≤ dj * ((cj - L) * (L + 6 - cj)) := by
    rw [← hV]
    have h_le : ∑ U ∈ domRank adj (A + 2), (((domCritical adj U).card : ℝ) - cj) ^ 2 ≤
        ∑ U ∈ domRank adj (A + 2),
          ((cj - L) * (L + 6 - cj) + (2 * L + 6 - 2 * cj) * (((domCritical adj U).card : ℝ) - cj)) := by
      apply Finset.sum_le_sum
      intro U hU
      have hprod : 0 ≤ (((domCritical adj U).card : ℝ) - L) * (L + 6 - ((domCritical adj U).card : ℝ)) :=
        mul_nonneg (sub_nonneg.mpr (h_bounds U hU).1) (sub_nonneg.mpr (h_bounds U hU).2)
      have hid : (cj - L) * (L + 6 - cj) + (2 * L + 6 - 2 * cj) * (((domCritical adj U).card : ℝ) - cj) -
          (((domCritical adj U).card : ℝ) - cj) ^ 2 =
          (((domCritical adj U).card : ℝ) - L) * (L + 6 - ((domCritical adj U).card : ℝ)) := by ring
      linarith
    have h_eq : ∑ U ∈ domRank adj (A + 2),
          ((cj - L) * (L + 6 - cj) + (2 * L + 6 - 2 * cj) * (((domCritical adj U).card : ℝ) - cj)) =
        dj * ((cj - L) * (L + 6 - cj)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, h_mean, hcard]
      ring
    linarith
  have h_var : critVar adj (A + 2) ≤ (cj - L) * (L + 6 - cj) := le_of_mul_le_mul_left h_bd hd_j
  -- jump bound
  have h_den : 2 ≤ ((A : ℝ) + 2) - cj := by linarith
  have h_quad : (cj - L) * (L + 6 - cj) ≤ 2 * (((A : ℝ) + 2) - cj) := by
    have e4 : 2 * (((A : ℝ) + 2) - cj) - (cj - L) * (L + 6 - cj) =
        (cj - L - 4) ^ 2 + 2 * (((A : ℝ) + 2) - L) - 16 := by ring
    have hs := sq_nonneg (cj - L - 4)
    linarith
  have h_jump : cj - ci ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < (((A : ℝ) + 2) - cj) * (cj - ci - 2) := mul_pos (by linarith) (by linarith)
    have e3 : (((A : ℝ) + 2) - cj) * (cj - ci - 2) =
        (((A : ℝ) + 2) - cj) * (cj - ci) - 2 * (((A : ℝ) + 2) - cj) := by ring
    linarith
  -- strict valley exclusion
  have hn1 : ((A : ℝ) + 2) ≤ (Fintype.card α : ℝ) := by exact_mod_cast h_jn
  have h_no_valley : ¬ (di < dR adj A ∧ di < dj) := by
    rintro ⟨h1, h2⟩
    have hq1 : ((Fintype.card α : ℝ) - A) * (di - dR adj A) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have hq2 : ((Fintype.card α : ℝ) - ((A : ℝ) + 1)) * (di - dj) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have hc1 : ci < 2 * (A : ℝ) + 1 - (Fintype.card α : ℝ) := by
      have e1 : di * (2 * (A : ℝ) + 1 - (Fintype.card α : ℝ)) =
          di * ((A : ℝ) + 1) - ((Fintype.card α : ℝ) - A) * di := by ring
      have e2 : ((Fintype.card α : ℝ) - A) * (di - dR adj A) =
          ((Fintype.card α : ℝ) - A) * di - ((Fintype.card α : ℝ) - A) * dR adj A := by ring
      have key : di * ci < di * (2 * (A : ℝ) + 1 - (Fintype.card α : ℝ)) := by
        rw [e1]; linarith
      exact lt_of_mul_lt_mul_left key hd_i.le
    have hc2 : 2 * (A : ℝ) + 3 - (Fintype.card α : ℝ) < cj := by
      have e1 : dj * (2 * (A : ℝ) + 3 - (Fintype.card α : ℝ)) =
          dj * ((A : ℝ) + 2) - ((Fintype.card α : ℝ) - ((A : ℝ) + 1)) * dj := by ring
      have e2 : ((Fintype.card α : ℝ) - ((A : ℝ) + 1)) * (di - dj) =
          ((Fintype.card α : ℝ) - ((A : ℝ) + 1)) * di -
            ((Fintype.card α : ℝ) - ((A : ℝ) + 1)) * dj := by ring
      have key : dj * (2 * (A : ℝ) + 3 - (Fintype.card α : ℝ)) < dj * cj := by
        rw [e1]; linarith
      exact lt_of_mul_lt_mul_left key hd_j.le
    linarith
  refine ⟨h_jump, h_no_valley, ?_⟩
  by_cases h1 : dR adj A ≤ dR adj (A + 1)
  · by_cases h2 : dR adj (A + 1) ≤ dR adj (A + 2)
    · refine ⟨A + 2, ?_, ?_⟩
      · intro k hk
        rcases lt_trichotomy k A with hlt | rfl | hgt
        · exact h_left k hlt
        · exact h1
        · have hkA1 : k = A + 1 := by omega
          rw [hkA1]
          exact h2
      · intro k hk
        exact h_right k hk
    · push_neg at h2
      refine ⟨A + 1, ?_, ?_⟩
      · intro k hk
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
        · exact h_left k hlt
        · exact h1
      · intro k hk
        rcases eq_or_lt_of_le hk with rfl | hgt
        · exact le_of_lt h2
        · exact h_right k (Nat.succ_le_of_lt hgt)
  · push_neg at h1
    have h2 : dR adj (A + 2) ≤ dR adj (A + 1) := by
      by_contra h2_neg
      push_neg at h2_neg
      exact h_no_valley ⟨h1, h2_neg⟩
    refine ⟨A, ?_, ?_⟩
    · intro k hk
      exact h_left k hk
    · intro k hk
      rcases eq_or_lt_of_le hk with rfl | hgt
      · exact le_of_lt h1
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with hA1 | hgt2
        · rw [← hA1]
          exact h2
        · exact h_right k (Nat.succ_le_of_lt hgt2)

end GapThreeGraphConnectionAudit
