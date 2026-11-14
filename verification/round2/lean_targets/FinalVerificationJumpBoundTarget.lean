import Mathlib
import domination_gap3.GraphConnectionTheoremCandidate

/-! Fixed proposition 7.2(i) from the submitted manuscript, with the
strict bound at every index gamma < j < n. -/

namespace FinalVerificationJumpBound
open GapThreeGraphConnectionAudit

theorem forest_critical_jump_strict_upper_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic)
    (γ : ℕ) (S0 : Finset α)
    (hS0 : IsDominating G.Adj S0) (hS0card : S0.card ≤ γ)
    (hγmin : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (j : ℕ) (hγj : γ < j) (hjn : j < Fintype.card α) :
    critMean G.Adj (j + 1) - critMean G.Adj j <
      2 * ((j : ℝ) - (γ : ℝ)) + 1 := by
  sorry

end FinalVerificationJumpBound
