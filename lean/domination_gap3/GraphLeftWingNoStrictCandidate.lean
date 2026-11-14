import Mathlib
import domination_gap3.GraphUniformGapNoStrictCandidate

namespace GraphLeftWingNoStrictAudit
open GapThreeGraphConnectionAudit

theorem left_wing_from_critical_lower
    {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (γ A : ℕ)
    (hAle : A ≤ Fintype.card α)
    (hwing : 3 * A ≤ Fintype.card α + 2 * γ + 1)
    (hlower : ∀ j, ∀ U ∈ domRank adj j,
      2 * (γ : ℝ) - (j : ℝ) ≤ ((domCritical adj U).card : ℝ)) :
    ∀ k < A, dR adj k ≤ dR adj (k + 1) := by
  intro k hk
  let n := Fintype.card α
  have hkN : k < n := by dsimp [n]; omega
  have hpos : 0 < n - k := by omega
  have hcoef : 2 * (k + 1) ≤ (n - k) + 2 * γ := by omega
  have hc : ∀ U ∈ domRank adj (k + 1),
      2 * γ ≤ (k + 1) + (domCritical adj U).card := by
    intro U hU
    have hr := hlower (k + 1) U hU
    have hr' : (2 * γ : ℕ) ≤ (k + 1) + (domCritical adj U).card := by
      exact_mod_cast (show (2 * (γ : ℝ)) ≤
        (((k + 1 : ℕ) : ℝ) + ((domCritical adj U).card : ℝ)) by linarith)
    exact hr'
  have hs : (∑ U ∈ domRank adj (k + 1), 2 * γ) ≤
      (∑ U ∈ domRank adj (k + 1), ((k + 1) + (domCritical adj U).card)) := by
    apply Finset.sum_le_sum
    intro U hU
    exact hc U hU
  have hsum : (2 * γ) * (domRank adj (k + 1)).card ≤
      (k + 1) * (domRank adj (k + 1)).card +
        (∑ U ∈ domRank adj (k + 1), (domCritical adj U).card) := by
    simpa [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]
      using hs
  letI : DecidablePred (GapThreeGraphLevelSynthesisAudit.IsDominating adj) :=
    inferInstanceAs (DecidablePred (IsDominating adj))
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
  have he : (∑ U ∈ domRank adj (k + 1), (domCritical adj U).card) +
      (n - k) * (domRank adj k).card =
      (domRank adj (k + 1)).card * (k + 1) := by
    have hnat := GapThreeGraphLevelSynthesisAudit.graph_domination_lemma3_identity
      adj (k + 1) (by omega)
    simpa [hrank, hcrit, n] using hnat
  have hcoefm : (2 * (k + 1)) * (domRank adj (k + 1)).card ≤
      ((n - k) + 2 * γ) * (domRank adj (k + 1)).card :=
    Nat.mul_le_mul_right _ hcoef
  have hmon : (domRank adj k).card ≤ (domRank adj (k + 1)).card := by
    by_contra h
    have hbad : (domRank adj (k + 1)).card < (domRank adj k).card :=
      Nat.lt_of_not_ge h
    have hmul : (n - k) * (domRank adj (k + 1)).card <
        (n - k) * (domRank adj k).card :=
      Nat.mul_lt_mul_of_pos_left hbad hpos
    nlinarith
  change ((domRank adj k).card : ℝ) ≤ ((domRank adj (k + 1)).card : ℝ)
  exact_mod_cast hmon

end GraphLeftWingNoStrictAudit
