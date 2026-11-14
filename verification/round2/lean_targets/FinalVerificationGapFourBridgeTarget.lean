import Mathlib
import domination_gap3.GapFourFiniteReductionCandidate
import domination_gap3.FinalVerificationIsolatesCandidate

/-! Fixed conditional target: all isolates and large orders are discharged
by analytic Lean theorems, provided the explicit ≤22 finite case is certified.
The full unconditional target in GapFourFullTarget.lean is unchanged. -/

namespace FinalVerificationGapFourBridge
open GapThreeGraphConnectionAudit
open FinalVerificationIsolates

theorem forest_gap_four_of_finite_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic)
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w)
    (γ : ℕ) (S0 M : Finset α)
    (hS0 : IsDominating G.Adj S0) (hS0card : S0.card ≤ γ)
    (hγmin : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (hM : IsDominating G.Adj M)
    (hMminimal : ∀ v ∈ M, ¬ IsDominating G.Adj (M.erase v))
    (hMcard : M.card = γ + 4)
    (hΓmax : ∀ N : Finset α, IsDominating G.Adj N →
      (∀ v ∈ N, ¬ IsDominating G.Adj (N.erase v)) → N.card ≤ γ + 4)
    (hsmall : Fintype.card {v : α // v ∉ I} ≤ 22 →
      IsWeakUnimodal (reducedDR G I)) :
    IsWeakUnimodal (dR G.Adj) := by
  sorry

end FinalVerificationGapFourBridge
