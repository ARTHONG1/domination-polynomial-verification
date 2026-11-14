import Mathlib
import domination_gap3.FinalVerificationGapThreeAllBridgeCandidate

namespace FinalVerificationGapThreeFull
open GapThreeGraphConnectionAudit FinalVerificationIsolates

theorem forest_gap_le_three_unimodal
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic)
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
  classical
  let I : Finset α := Finset.univ.filter (fun v => ∀ w, ¬ G.Adj v w)
  have hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w := by
    intro v
    simp [I]
  let H : SimpleGraph {v : α // v ∉ I} := G.induce {v | v ∉ I}
  have hforestH : H.IsAcyclic := hforest.induce _
  have hnoisoH : ∀ v, ∃ u, H.Adj v u := by
    intro v
    have hvLive : ∃ u : α, G.Adj v.1 u := by
      by_contra hc
      push_neg at hc
      exact v.2 ((hI v.1).mpr hc)
    obtain ⟨u, hadj⟩ := hvLive
    have huLive : u ∉ I := by
      intro huI
      exact ((hI u).mp huI v.1) (G.symm hadj)
    exact ⟨⟨u, huLive⟩, hadj⟩
  obtain ⟨T, hTdom, hTγ, hTminShift⟩ :=
    domination_number_isolate_shift G I hI γ S0 hS0 hS0card hγmin
  obtain ⟨N, hNdom, hNmin, hNΓ, hNmaxShift⟩ :=
    upper_domination_number_isolate_shift G I hI (γ + h)
      M hM hMminimal hMcard hΓmax
  have hTmin : ∀ U : Finset {v : α // v ∉ I},
      IsDominating H.Adj U → T.card ≤ U.card := by
    intro U hU
    have hb := hTminShift U hU
    omega
  have hNcard : N.card = T.card + h := by omega
  have hNmax : ∀ U : Finset {v : α // v ∉ I},
      IsDominating H.Adj U →
      (∀ v ∈ U, ¬ IsDominating H.Adj (U.erase v)) →
      U.card ≤ T.card + h := by
    intro U hU hmin
    have hb := hNmaxShift U hU hmin
    omega
  have hred := FinalVerificationGapThreeAllBridge.no_isolates_gap_le_three
    H hforestH hnoisoH T.card h T N hTdom (le_refl _) hTmin
    hNdom hNmin hNcard hNmax hh
  have hred' : IsWeakUnimodal (reducedDR G I) := by
    simpa [IsWeakUnimodal, reducedDR, reducedRankCard, dR, H] using hred
  exact (domination_isolate_unimodal_iff G I hI).mpr hred'

#print axioms forest_gap_le_three_unimodal

end FinalVerificationGapThreeFull
