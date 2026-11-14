import Mathlib
import domination_gap3.GapFourFiniteReductionCandidate
import domination_gap3.FinalVerificationIsolatesCandidate

/-! Submitted-paper P14: the full gap-four result is reduced to an explicit
finite small-case premise, including arbitrary isolated vertices. This file
does NOT assert that the small-case premise has been kernel-certified. -/

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
  classical
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
    upper_domination_number_isolate_shift G I hI (γ + 4)
      M hM hMminimal hMcard hΓmax
  have hTmin : ∀ U : Finset {v : α // v ∉ I},
      IsDominating H.Adj U → T.card ≤ U.card := by
    intro U hU
    have hb := hTminShift U hU
    omega
  have hNcard : N.card = T.card + 4 := by omega
  have hNmax : ∀ U : Finset {v : α // v ∉ I},
      IsDominating H.Adj U →
      (∀ v ∈ U, ¬ IsDominating H.Adj (U.erase v)) →
      U.card ≤ T.card + 4 := by
    intro U hU hmin
    have hb := hNmaxShift U hU hmin
    omega
  have hcase := GapFourFiniteReductionAudit.no_isolates_gap_four_large_or_at_most_twenty_two
    H hnoisoH T.card N hTmin hNdom hNmin hNcard
  have hreduce : IsWeakUnimodal (reducedDR G I) := by
    rcases hcase with hlarge | hsmallbound
    · have hu := GapFourForestLargeAudit.forest_gap_four_large_unimodal
        H hforestH T.card T hTdom (le_refl _) hTmin hNmax hlarge
      simpa [IsWeakUnimodal, reducedDR, reducedRankCard, dR, H] using hu
    · exact hsmall hsmallbound
  exact (domination_isolate_unimodal_iff G I hI).mpr hreduce

end FinalVerificationGapFourBridge
