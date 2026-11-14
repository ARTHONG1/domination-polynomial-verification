import Mathlib
import domination_gap3.GraphDominationBijectionCandidate
import domination_gap3.ForestGapThreeLargeNoMatchingCandidate
import domination_gap3.BipartiteCriticalIndependentCandidate

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
  classical
  have hcomp : IsDominating G.Adj (Finset.univ \ M) := by
    exact GapThreeGraphDominationAudit.isDominating_compl_of_minimal
      G.Adj (fun v hv => G.irrefl hv)
      (fun u v huv => G.symm huv) hnoiso M hM hMminimal
  have hγ := hγmin (Finset.univ \ M) hcomp
  have hcard : (Finset.univ \ M).card = Fintype.card α - M.card := by
    simp [Finset.card_sdiff]
  have hMle : M.card ≤ Fintype.card α := by
    simpa using Finset.card_le_card (Finset.subset_univ M)
  omega

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
  classical
  have hcrit : domCritical G.Adj M = M := by
    ext x
    simp only [domCritical, Finset.mem_filter]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hMminimal x hx⟩⟩
  have hle : Γ ≤ G.indepNum := by
    have hb := BipartiteCriticalIndependentAudit.bipartite_critical_le_two_independence
      G hbi M hM
    rw [hcrit, hMsize] at hb
    omega
  have hge : G.indepNum ≤ Γ :=
    ForestGapThreeLargeNoMatchingAudit.independence_le_maximal_domination
      G Γ hΓmax
  omega

end FinalVerificationOreAlpha
