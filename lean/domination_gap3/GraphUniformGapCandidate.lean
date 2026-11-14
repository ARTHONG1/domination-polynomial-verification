import Mathlib
import domination_gap3.FiniteUniformVarianceCandidate
import domination_gap3.UniformGapGlobalCandidate
import domination_gap3.GraphConnectionTheoremCandidate
import domination_gap3.GraphLevelIncidenceTheoremCandidate

namespace GraphUniformGapAudit
open GapThreeGraphConnectionAudit

private lemma dom_up {α : Type*} (adj : α → α → Prop)
    {S U : Finset α} (hsub : S ⊆ U) (hS : IsDominating adj S) :
    IsDominating adj U := by
  intro v
  rcases hS v with hv | ⟨u, hu, huv⟩
  · exact Or.inl (hsub hv)
  · exact Or.inr ⟨u, hsub hu, huv⟩

private lemma rank_pos {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    {S0 : Finset α} (hS0 : IsDominating adj S0) {j : ℕ}
    (hlow : S0.card ≤ j) (hhigh : j ≤ Fintype.card α) :
    0 < dR adj j := by
  obtain ⟨U, hsub, hUcard⟩ := Finset.exists_superset_card_eq hlow hhigh
  have hmem : U ∈ domRank adj j := by
    rw [domRank, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hUcard, dom_up adj hsub hS0⟩
  unfold dR
  exact_mod_cast Finset.card_pos.mpr ⟨U, hmem⟩

private lemma rank_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (j : ℕ) :
    0 ≤ dR adj j := by unfold dR; positivity

private lemma rank_zero_tail {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (j : ℕ)
    (hj : Fintype.card α < j) : dR adj j = 0 := by
  have he : domRank adj j = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro S hS
    rw [domRank, Finset.mem_filter] at hS
    have hh := Finset.card_le_univ S
    omega
  simp [dR, he]

private lemma sum_eq_d_mul_mean {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (j : ℕ) :
    critSum adj j = dR adj j * critMean adj j := by
  by_cases hs : (domRank adj j).Nonempty
  · have hd : 0 < dR adj j := by
      unfold dR
      exact_mod_cast Finset.card_pos.mpr hs
    have hne : dR adj j ≠ 0 := ne_of_gt hd
    unfold critMean
    field_simp
  · have he : domRank adj j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [critMean, critSum, dR, he]

/-- A finite-graph realization of the uniform bounded-gap unimodality criterion.
The tree-specific critical inequalities and the published left wing are explicit inputs. -/
theorem graph_uniform_gap_unimodal
    {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (γ h K A : ℕ) (S0 : Finset α)
    (hS0 : IsDominating adj S0) (hS0card : S0.card ≤ γ)
    (hK : h < K) (hquad : (h + 1) ^ 2 ≤ 4 * K)
    (hcut : γ + K ≤ A + 2) (hAn : A + 2 ≤ Fintype.card α)
    (hleft : ∀ k < A, dR adj k ≤ dR adj (k + 1))
    (hcritical : ∀ j, ∀ U ∈ domRank adj j,
      2 * (γ : ℝ) - (j : ℝ) ≤ ((domCritical adj U).card : ℝ) ∧
      ((domCritical adj U).card : ℝ) ≤
        2 * (γ : ℝ) - (j : ℝ) + 2 * (h : ℝ)) :
    ∃ m : ℕ, (∀ k < m, dR adj k ≤ dR adj (k + 1)) ∧
      (∀ k ≥ m, dR adj (k + 1) ≤ dR adj k) := by
  have hpop : ∀ j, γ + K ≤ j → j ≤ Fintype.card α →
      (2 * (γ : ℝ) - (j : ℝ) ≤ critMean adj j ∧
        critMean adj j ≤ 2 * (γ : ℝ) - (j : ℝ) + 2 * (h : ℝ)) ∧
      critVar adj j ≤ (critMean adj j - (2 * (γ : ℝ) - (j : ℝ))) *
        (2 * (γ : ℝ) - (j : ℝ) + 2 * (h : ℝ) - critMean adj j) := by
    intro j hj hjn
    have hjgamma : γ ≤ j := by omega
    have hd : 0 < dR adj j := rank_pos adj hS0 (by omega) hjn
    have hs : (domRank adj j).Nonempty := by
      apply Finset.card_pos.mp
      change 0 < ((domRank adj j).card : ℝ) at hd
      exact_mod_cast hd
    have hbounded := FiniteUniformVarianceAudit.finite_uniform_variance_bound
      (domRank adj j) (fun U => ((domCritical adj U).card : ℝ))
      (2 * (γ : ℝ) - (j : ℝ))
      (2 * (γ : ℝ) - (j : ℝ) + 2 * (h : ℝ))
      hs (hcritical j)
    constructor
    · constructor
      · simpa only [critMean, critSum, dR] using hbounded.1
      · simpa only [critMean, critSum, dR] using hbounded.2.1
    · simpa only [critMean, critVar, critSum, dR] using hbounded.2.2
  apply UniformGapGlobalAudit.weak_unimodal_of_uniform_rank_data
    (dR adj) (critMean adj) (critVar adj) (Fintype.card α) A γ h K
    hK hquad hcut hAn hleft
  · intro j hjlo hjn
    exact rank_pos adj hS0 (by omega) hjn
  · intro j
    exact rank_nonneg adj j
  · intro j hj
    exact rank_zero_tail adj j hj
  · intro i hi
    classical
    have hrank (j : ℕ) :
        GapThreeGraphLevelSynthesisAudit.domRank adj j = domRank adj j := by
      ext S
      simp only [GapThreeGraphLevelSynthesisAudit.domRank, domRank,
        Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    have hcrit (S : Finset α) :
        GapThreeGraphLevelSynthesisAudit.domCritical adj S = domCritical adj S := by
      ext x
      simp only [GapThreeGraphLevelSynthesisAudit.domCritical, domCritical,
        Finset.mem_filter]
      rfl
    have hnat := GapThreeGraphLevelSynthesisAudit.graph_domination_lemma3_identity
      adj (i + 1) (by omega)
    have he : (∑ U ∈ domRank adj (i + 1), (domCritical adj U).card) +
        (Fintype.card α - i) * (domRank adj i).card =
        (domRank adj (i + 1)).card * (i + 1) := by
      simpa only [hrank, hcrit] using hnat
    have hreal := congrArg (fun q : ℕ => (q : ℝ)) he
    have hle : i ≤ Fintype.card α := by omega
    push_cast [Nat.cast_sub hle] at hreal
    have hm := sum_eq_d_mul_mean adj (i + 1)
    dsimp [critSum, dR] at hm
    dsimp [dR] at hreal ⊢
    rw [hm] at hreal
    push_cast at hreal ⊢
    nlinarith
  · intro j hj hjn
    exact (hpop j hj hjn).1
  · intro j hj hjn
    exact (hpop j hj hjn).2
  · intro j hj hjn
    have hjpos : 1 ≤ j := by omega
    have hprev : S0.card ≤ j - 1 := by omega
    have hprevpos : 0 < dR adj (j - 1) :=
      rank_pos adj hS0 hprev (by omega)
    have hjpos' : 0 < dR adj j :=
      rank_pos adj hS0 (by omega) hjn
    have hjsucc : j - 1 + 1 = j := by omega
    have hreal : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
      exact_mod_cast hjsucc
    have hinc := GapThreeGraphConnectionAudit.graph_incidence_variance_inequality
      adj (j - 1) (by omega) hprevpos (by simpa [hjsucc] using hjpos')
    simpa only [hjsucc, hreal] using hinc

end GraphUniformGapAudit
