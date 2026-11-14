import Mathlib
import domination_gap3.GraphCriticalGapThreeLargeCandidate
import domination_gap3.BipartiteCriticalIndependentCandidate
import domination_gap3.ForestConflictCountBridgeCandidate

namespace ForestGapThreeLargeNoMatchingAudit
open GapThreeGraphConnectionAudit

private theorem maximum_independent_is_minimal_dominating
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (M : Finset α)
    (hmax : G.IsMaximumIndepSet M) :
    IsDominating G.Adj M ∧
      (∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x)) := by
  classical
  have hindep := hmax.isIndepSet
  have hdom : IsDominating G.Adj M := by
    intro v
    by_contra hn
    have hvnot : v ∉ M := by
      intro hv
      exact hn (Or.inl hv)
    have hnoadj : ∀ u ∈ M, ¬G.Adj v u := by
      intro u hu hadj
      exact hn (Or.inr ⟨u, hu, hadj⟩)
    have hplus : G.IsIndepSet (↑(insert v M) : Set α) := by
      intro x hx y hy hxy hadj
      have hx' : x ∈ insert v M := hx
      have hy' : y ∈ insert v M := hy
      rcases Finset.mem_insert.mp hx' with rfl | hxM
      · rcases Finset.mem_insert.mp hy' with rfl | hyM
        · exact hxy rfl
        · exact hnoadj y hyM hadj
      · rcases Finset.mem_insert.mp hy' with rfl | hyM
        · exact hnoadj x hxM hadj.symm
        · exact hindep hxM hyM hxy hadj
    have hb := hmax.maximum (insert v M) hplus
    have hcard : (insert v M).card = M.card + 1 :=
      Finset.card_insert_of_notMem hvnot
    omega
  refine ⟨hdom, ?_⟩
  intro x hx hdel
  rcases hdel x with hxdel | ⟨u, hu, hxu⟩
  · have hnot : x ∉ M.erase x := by simp
    exact hnot hxdel
  · have hu' := Finset.mem_erase.mp hu
    exact hindep hx hu'.2 hu'.1.symm hxu

theorem independence_le_maximal_domination
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (Γ : ℕ)
    (hΓ_max : ∀ M : Finset α, IsDominating G.Adj M →
      (∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x)) → M.card ≤ Γ) :
    G.indepNum ≤ Γ := by
  obtain ⟨M, hmax⟩ := G.maximumIndepSet_exists
  have hminimal := maximum_independent_is_minimal_dominating G M hmax
  calc
    G.indepNum = M.card := (G.maximumIndepSet_card_eq_indepNum M hmax).symm
    _ ≤ Γ := hΓ_max M hminimal.1 hminimal.2

theorem bipartite_critical_le_two_upperdom
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hbi : G.IsBipartite) (Γ : ℕ)
    (hΓ_max : ∀ M : Finset α, IsDominating G.Adj M →
      (∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x)) → M.card ≤ Γ)
    (S : Finset α) (hS : IsDominating G.Adj S) :
    S.card + (domCritical G.Adj S).card ≤ 2 * Γ := by
  calc
    S.card + (domCritical G.Adj S).card ≤ 2 * G.indepNum :=
      BipartiteCriticalIndependentAudit.bipartite_critical_le_two_independence
        G hbi S hS
    _ ≤ 2 * Γ := Nat.mul_le_mul_left 2
      (independence_le_maximal_domination G Γ hΓ_max)

theorem forest_gap_three_large_unimodal
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic) (γ : ℕ) (S0 : Finset α)
    (hS0 : IsDominating G.Adj S0) (hS0card : S0.card ≤ γ)
    (hγ_min : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (hΓ_max : ∀ M : Finset α, IsDominating G.Adj M →
      (∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x)) → M.card ≤ γ + 3)
    (hn : γ + 5 ≤ Fintype.card α) :
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
      ((domCritical G.Adj U).card : ℝ) ≤ 2 * (γ : ℝ) - (j : ℝ) + 6 := by
    intro j U hU
    have hj : U.card = j := (Finset.mem_filter.mp hU).2.1
    have hdom : IsDominating G.Adj U := (Finset.mem_filter.mp hU).2.2
    have hnat := bipartite_critical_le_two_upperdom G hforest.isBipartite
      (γ + 3) hΓ_max U hdom
    have hnat' : j + (domCritical G.Adj U).card ≤ 2 * (γ + 3) := by
      simpa [hj] using hnat
    have hr : (j : ℝ) + ((domCritical G.Adj U).card : ℝ) ≤
        2 * ((γ : ℝ) + 3) := by
      exact_mod_cast hnat'
    linarith
  exact GraphCriticalGapThreeLargeAudit.gap_three_large_from_critical_bounds
    G.Adj γ S0 hS0 hS0card hn hlower hupper

end ForestGapThreeLargeNoMatchingAudit
