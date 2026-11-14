import Mathlib
import domination_gap3.GraphDominationBijectionCandidate
import domination_gap3.ForestGapThreeLargeNoMatchingCandidate

/-! Immutable statements for submitted-paper checks P2 and P6.
    The proof candidates are in FinalVerificationOreAlphaCandidate. -/

namespace FinalVerificationOreAlpha
open GapThreeGraphConnectionAudit

theorem ore_gamma_plus_upperdom_le_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hnoiso : ∀ v, ∃ u, G.Adj v u)
    (γ Γ : ℕ)
    (hγmin : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (M : Finset α)
    (hM : IsDominating G.Adj M)
    (hMminimal : ∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x))
    (hMsize : M.card = Γ) :
    γ + Γ ≤ Fintype.card α := by
  sorry

theorem bipartite_upperdom_eq_independence
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hbi : G.IsBipartite)
    (Γ : ℕ)
    (M : Finset α)
    (hM : IsDominating G.Adj M)
    (hMminimal : ∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x))
    (hMsize : M.card = Γ)
    (hΓmax : ∀ N : Finset α, IsDominating G.Adj N →
      (∀ x ∈ N, ¬ IsDominating G.Adj (N.erase x)) → N.card ≤ Γ) :
    Γ = G.indepNum := by
  sorry

end FinalVerificationOreAlpha
