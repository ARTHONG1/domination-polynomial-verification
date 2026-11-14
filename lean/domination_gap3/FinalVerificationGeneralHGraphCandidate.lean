import Mathlib
import domination_gap3.FinalVerificationGapArithmeticCandidate
import domination_gap3.GraphLeftWingNoStrictCandidate

/-!
The submitted Theorem 5.1 for an arbitrary finite graph satisfying H_h.
The actual domination number is pinned by hS0, hS0card and hγmin.
The graph hypothesis H_h is written pointwise over each dominating set.
This avoids the stronger h<K and A+2≤n assumptions of the earlier audit.
-/

namespace FinalVerificationGeneralHGraph
open GapThreeGraphConnectionAudit

theorem graph_unimodal_of_Hh_large
    {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (γ h : ℕ) (S0 : Finset α)
    (hS0 : IsDominating adj S0) (hS0card : S0.card ≤ γ)
    (hγmin : ∀ S : Finset α, IsDominating adj S → γ ≤ S.card)
    (hH : ∀ S : Finset α, IsDominating adj S →
      2 * (γ : ℝ) - (S.card : ℝ) ≤ ((domCritical adj S).card : ℝ) ∧
      ((domCritical adj S).card : ℝ) ≤
        2 * (γ : ℝ) - (S.card : ℝ) + 2 * (h : ℝ))
    (hlarge : γ + 3 * FinalVerificationGapArithmetic.K h ≤
      Fintype.card α + 7) :
    ∃ m : ℕ, (∀ k < m, dR adj k ≤ dR adj (k + 1)) ∧
      (∀ k ≥ m, dR adj (k + 1) ≤ dR adj k) := by
  let K := FinalVerificationGapArithmetic.K h
  let A := (Fintype.card α + 2 * γ + 1) / 3
  have hγn : γ ≤ Fintype.card α := by
    have hp := hγmin S0 hS0
    have hc := Finset.card_le_univ S0
    omega
  have hKpos : 0 < K := by
    have hsquare : 0 < (h + 1) ^ 2 := pow_pos (Nat.succ_pos h) _
    have hc := (FinalVerificationGapArithmetic.K_is_ceil h).1
    dsimp [K]
    omega
  have hquad : (h + 1) ^ 2 ≤ 4 * K :=
    (FinalVerificationGapArithmetic.K_is_ceil h).1
  have hAle : A ≤ Fintype.card α := by
    dsimp [A]
    omega
  have hwing : 3 * A ≤ Fintype.card α + 2 * γ + 1 := by
    dsimp [A]
    omega
  have hcut : γ + K ≤ A + 2 := by
    dsimp [A, K] at *
    omega
  have hcritical : ∀ j, ∀ U ∈ domRank adj j,
      2 * (γ : ℝ) - (j : ℝ) ≤ ((domCritical adj U).card : ℝ) ∧
      ((domCritical adj U).card : ℝ) ≤
        2 * (γ : ℝ) - (j : ℝ) + 2 * (h : ℝ) := by
    intro j U hU
    have hUc : U.card = j := (Finset.mem_filter.mp hU).2.1
    have hUd : IsDominating adj U := (Finset.mem_filter.mp hU).2.2
    simpa only [hUc] using hH U hUd
  exact GraphUniformGapNoStrictAudit.graph_uniform_gap_unimodal_all_order
    adj γ h K A S0 hS0 hS0card hKpos hquad hcut hAle hγn
    (GraphLeftWingNoStrictAudit.left_wing_from_critical_lower
      adj γ A hAle hwing (fun j U hU => (hcritical j U hU).1))
    hcritical

#print axioms graph_unimodal_of_Hh_large

end FinalVerificationGeneralHGraph
