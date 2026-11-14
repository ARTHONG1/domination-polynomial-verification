import Mathlib
import domination_gap3.FinalVerificationGeneralHGraphCandidate
import domination_gap3.ForestGapThreeLargeNoMatchingCandidate

namespace FinalVerificationForestGeneralHBridge
open GapThreeGraphConnectionAudit

/-- Every finite forest has the precise pointwise H_h estimate from
Corollary 3.3 of the manuscript, when Γ(F) ≤ γ+h. -/
theorem forest_Hh_of_upperdom_gap
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic) (γ h : ℕ)
    (hγmin : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (hΓmax : ∀ N : Finset α, IsDominating G.Adj N →
      (∀ x ∈ N, ¬ IsDominating G.Adj (N.erase x)) → N.card ≤ γ + h) :
    ∀ S : Finset α, IsDominating G.Adj S →
      2 * (γ : ℝ) - (S.card : ℝ) ≤ ((domCritical G.Adj S).card : ℝ) ∧
      ((domCritical G.Adj S).card : ℝ) ≤
        2 * (γ : ℝ) - (S.card : ℝ) + 2 * (h : ℝ) := by
  classical
  have hγmin' : ∀ S : Finset α,
      GapThreeCriticalConflictCount.IsDominating G.Adj S → γ ≤ S.card := by
    intro S hS
    apply hγmin
    simpa only [IsDominating, GapThreeCriticalConflictCount.IsDominating] using hS
  have hL := GapThreeForestConflictCount.forest_critical_inequality
    G hforest γ hγmin'
  intro S hS
  have hS' : GapThreeCriticalConflictCount.IsDominating G.Adj S := by
    simpa only [IsDominating, GapThreeCriticalConflictCount.IsDominating] using hS
  have hlow : 2 * γ ≤ (domCritical G.Adj S).card + S.card := by
    convert hL S hS'
  have hupp : S.card + (domCritical G.Adj S).card ≤ 2 * (γ + h) :=
    ForestGapThreeLargeNoMatchingAudit.bipartite_critical_le_two_upperdom
      G hforest.isBipartite (γ + h) hΓmax S hS
  have hlow' : 2 * (γ : ℝ) ≤
      ((domCritical G.Adj S).card : ℝ) + (S.card : ℝ) := by
    exact_mod_cast hlow
  have hupp' : (S.card : ℝ) + ((domCritical G.Adj S).card : ℝ) ≤
      2 * ((γ : ℝ) + (h : ℝ)) := by
    exact_mod_cast hupp
  constructor <;> linarith

/-- Submitted Theorem 1.2(i), for all h including 0 and 1, with no
assumption excluding isolated vertices. -/
theorem forest_unimodal_of_large
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic) (γ h : ℕ) (S0 : Finset α)
    (hS0 : IsDominating G.Adj S0) (hS0card : S0.card ≤ γ)
    (hγmin : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (hΓmax : ∀ N : Finset α, IsDominating G.Adj N →
      (∀ x ∈ N, ¬ IsDominating G.Adj (N.erase x)) → N.card ≤ γ + h)
    (hlarge : γ + 3 * FinalVerificationGapArithmetic.K h ≤
      Fintype.card α + 7) :
    ∃ m : ℕ, (∀ k < m, dR G.Adj k ≤ dR G.Adj (k + 1)) ∧
      (∀ k ≥ m, dR G.Adj (k + 1) ≤ dR G.Adj k) := by
  exact FinalVerificationGeneralHGraph.graph_unimodal_of_Hh_large
    G.Adj γ h S0 hS0 hS0card hγmin
    (forest_Hh_of_upperdom_gap G hforest γ h hγmin hΓmax) hlarge

#print axioms forest_unimodal_of_large

end FinalVerificationForestGeneralHBridge
