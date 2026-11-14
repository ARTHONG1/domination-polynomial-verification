import Mathlib
import domination_gap3.FinalVerificationForestGeneralHBridgeCandidate
import domination_gap3.FinalVerificationOreAlphaCandidate
import domination_gap3.ForestGapThreeAllNoIsolatesCandidate
import domination_gap3.FinalVerificationIsolatesCandidate

/-! Submitted Corollary 5.2: all gap≤3 forests, including arbitrary
isolated vertices and the empty vertex type. -/

namespace FinalVerificationGapThreeAllBridge
open GapThreeGraphConnectionAudit FinalVerificationIsolates

theorem no_isolates_gap_le_three
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic) (hnoisolates : ∀ v, ∃ u, G.Adj v u)
    (γ h : ℕ) (S0 M : Finset α)
    (hS0 : IsDominating G.Adj S0) (hS0card : S0.card ≤ γ)
    (hγmin : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (hM : IsDominating G.Adj M)
    (hMminimal : ∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x))
    (hMcard : M.card = γ + h)
    (hΓmax : ∀ N : Finset α, IsDominating G.Adj N →
      (∀ x ∈ N, ¬ IsDominating G.Adj (N.erase x)) → N.card ≤ γ + h)
    (hh : h ≤ 3) :
    ∃ m : ℕ, (∀ k < m, dR G.Adj k ≤ dR G.Adj (k + 1)) ∧
      (∀ k ≥ m, dR G.Adj (k + 1) ≤ dR G.Adj k) := by
  by_cases hh3 : h = 3
  · subst h
    exact ForestGapThreeAllNoIsolatesAudit.forest_gap_three_unimodal_no_isolates
      G hforest hnoisolates γ S0 M hS0 hS0card hγmin hM hMminimal
      hMcard hΓmax
  · have hsmall : h ≤ 2 := by omega
    have hγn : γ ≤ Fintype.card α :=
      (hγmin S0 hS0).trans (Finset.card_le_univ S0)
    have hlarge : γ + 3 * FinalVerificationGapArithmetic.K h ≤
        Fintype.card α + 7 := by
      by_cases hh2 : h = 2
      · have hOre := FinalVerificationOreAlpha.ore_gamma_plus_upperdom_le_card
          G hnoisolates γ (γ + h) hγmin M hM hMminimal hMcard
        subst h
        norm_num [FinalVerificationGapArithmetic.K] at *
        omega
      · have hh01 : h ≤ 1 := by omega
        interval_cases h <;> norm_num [FinalVerificationGapArithmetic.K] <;> omega
    exact FinalVerificationForestGeneralHBridge.forest_unimodal_of_large
      G hforest γ h S0 hS0 hS0card hγmin hΓmax hlarge

end FinalVerificationGapThreeAllBridge
