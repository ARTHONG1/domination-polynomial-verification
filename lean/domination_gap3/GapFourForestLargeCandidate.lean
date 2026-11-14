import Mathlib
import domination_gap3.GapFourAnalyticCandidate
import domination_gap3.ForestGapThreeLargeNoMatchingCandidate

namespace GapFourForestLargeAudit
open GapThreeGraphConnectionAudit

theorem forest_gap_four_large_unimodal
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic) (γ : ℕ) (S0 : Finset α)
    (hS0 : IsDominating G.Adj S0) (hS0card : S0.card ≤ γ)
    (hγ_min : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (hΓ_max : ∀ M : Finset α, IsDominating G.Adj M →
      (∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x)) → M.card ≤ γ + 4)
    (hn : γ + 14 ≤ Fintype.card α) :
    ∃ m : ℕ, (∀ k < m, dR G.Adj k ≤ dR G.Adj (k + 1)) ∧
      (∀ k ≥ m, dR G.Adj (k + 1) ≤ dR G.Adj k) := by
  classical
  have hmin' : ∀ S : Finset α,
      GapThreeCriticalConflictCount.IsDominating G.Adj S → γ ≤ S.card := by
    intro S hS
    apply hγ_min
    simpa only [IsDominating, GapThreeCriticalConflictCount.IsDominating] using hS
  have hbound := GapThreeForestConflictCount.forest_critical_inequality
    G hforest γ hmin'
  have hlower : ∀ j, ∀ U ∈ domRank G.Adj j,
      2 * (γ : ℝ) - (j : ℝ) ≤ ((domCritical G.Adj U).card : ℝ) := by
    intro j U hU
    have hj : U.card = j := (Finset.mem_filter.mp hU).2.1
    have hdom : IsDominating G.Adj U := (Finset.mem_filter.mp hU).2.2
    have hnat : 2 * γ ≤ (domCritical G.Adj U).card + U.card := by
      convert hbound U (by
        simpa only [IsDominating, GapThreeCriticalConflictCount.IsDominating] using hdom)
    have hnat' : 2 * γ ≤ (domCritical G.Adj U).card + j := by
      simpa [hj] using hnat
    have hr : 2 * (γ : ℝ) ≤
        ((domCritical G.Adj U).card : ℝ) + (j : ℝ) := by
      exact_mod_cast hnat'
    linarith
  have hupper : ∀ j, ∀ U ∈ domRank G.Adj j,
      ((domCritical G.Adj U).card : ℝ) ≤ 2 * (γ : ℝ) - (j : ℝ) + 8 := by
    intro j U hU
    have hj : U.card = j := (Finset.mem_filter.mp hU).2.1
    have hdom : IsDominating G.Adj U := (Finset.mem_filter.mp hU).2.2
    have hnat := ForestGapThreeLargeNoMatchingAudit.bipartite_critical_le_two_upperdom G hforest.isBipartite
      (γ + 4) hΓ_max U hdom
    have hnat' : j + (domCritical G.Adj U).card ≤ 2 * (γ + 4) := by
      simpa [hj] using hnat
    have hr : (j : ℝ) + ((domCritical G.Adj U).card : ℝ) ≤
        2 * ((γ : ℝ) + 4) := by
      exact_mod_cast hnat'
    linarith
  exact GapFourAnalyticAudit.gap_four_large_from_critical_bounds
    G.Adj γ S0 hS0 hS0card hn hlower hupper


end GapFourForestLargeAudit
