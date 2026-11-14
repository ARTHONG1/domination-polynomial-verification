import Mathlib
import domination_gap3.GapFourForestLargeCandidate
import domination_gap3.GraphDominationBijectionCandidate

/-!
First verified bridge toward the fixed full Gap-4 target.  The existing
large-order theorem is already kernel checked.  For an isolate-free graph
with exact upper domination gap four, the remaining case has at most 22
vertices.  This file does not certify the finite boundary itself.
-/

namespace GapFourFiniteReductionAudit
open GapThreeGraphConnectionAudit

/-- Under exact gap four and no isolates, either the analytic criterion
applies or the entire vertex set has size at most 22. -/
theorem no_isolates_gap_four_large_or_at_most_twenty_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hnoisolates : ∀ v, ∃ u, G.Adj v u)
    (γ : ℕ) (M : Finset α)
    (hγ_min : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (hM : IsDominating G.Adj M)
    (hMminimal : ∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x))
    (hMcard : M.card = γ + 4) :
    γ + 14 ≤ Fintype.card α ∨ Fintype.card α ≤ 22 := by
  classical
  have hcomplement : IsDominating G.Adj (Finset.univ \ M) := by
    exact GapThreeGraphDominationAudit.isDominating_compl_of_minimal
      G.Adj (fun _ hxx => G.irrefl hxx)
      (fun u v huv => G.symm huv)
      hnoisolates M hM hMminimal
  have hcompcard : γ ≤ (Finset.univ \ M).card := hγ_min _ hcomplement
  have hMle : M.card ≤ Fintype.card α := by
    simpa using Finset.card_le_card (Finset.subset_univ M)
  have heq : (Finset.univ \ M).card = Fintype.card α - M.card := by
    simp [Finset.card_sdiff]
  have hbound : 2 * γ + 4 ≤ Fintype.card α := by
    omega
  by_cases hlarge : γ + 14 ≤ Fintype.card α
  · exact Or.inl hlarge
  · right
    omega

/-- The exact remaining obligation for an isolate-free Gap-4 forest,
without silently promoting a C++ certificate to a Lean assumption. -/
theorem no_isolates_gap_four_of_certified_small_case
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic) (hnoisolates : ∀ v, ∃ u, G.Adj v u)
    (γ : ℕ) (S0 M : Finset α)
    (hS0 : IsDominating G.Adj S0) (hS0card : S0.card ≤ γ)
    (hγ_min : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (hM : IsDominating G.Adj M)
    (hMminimal : ∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x))
    (hMcard : M.card = γ + 4)
    (hΓ_max : ∀ N : Finset α, IsDominating G.Adj N →
      (∀ x ∈ N, ¬ IsDominating G.Adj (N.erase x)) → N.card ≤ γ + 4)
    (hsmall_case : Fintype.card α ≤ 22 →
      ∃ m : ℕ, (∀ k < m, dR G.Adj k ≤ dR G.Adj (k + 1)) ∧
        (∀ k ≥ m, dR G.Adj (k + 1) ≤ dR G.Adj k)) :
    ∃ m : ℕ, (∀ k < m, dR G.Adj k ≤ dR G.Adj (k + 1)) ∧
      (∀ k ≥ m, dR G.Adj (k + 1) ≤ dR G.Adj k) := by
  rcases no_isolates_gap_four_large_or_at_most_twenty_two
    G hnoisolates γ M hγ_min hM hMminimal hMcard with hlarge | hsmall
  · exact GapFourForestLargeAudit.forest_gap_four_large_unimodal
      G hforest γ S0 hS0 hS0card hγ_min hΓ_max hlarge
  · exact hsmall_case hsmall

end GapFourFiniteReductionAudit
