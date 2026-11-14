import Mathlib
import domination_gap3.GraphConnectionTheoremCandidate
import domination_gap3.GraphLevelIncidenceTheoremCandidate
import domination_gap3.ForestConflictCountBridgeCandidate

/-! Submitted Proposition 7.2(i): sharp strict critical-mean jump bound
for forests, for every gamma < j < n. -/

namespace FinalVerificationJumpBound
open GapThreeGraphConnectionAudit

private theorem rank_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (S0 : Finset α) (hS0 : IsDominating adj S0)
    (j : ℕ) (hsize : S0.card ≤ j) (hjn : j ≤ Fintype.card α) :
    0 < dR adj j := by
  classical
  obtain ⟨U, hsub, hsizeU⟩ := Finset.exists_superset_card_eq hsize hjn
  have hdomU : IsDominating adj U := by
    intro v
    rcases hS0 v with hv | ⟨u, hu, hadj⟩
    · exact Or.inl (hsub hv)
    · exact Or.inr ⟨u, hsub hu, hadj⟩
  have hmem : U ∈ domRank adj j :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsizeU, hdomU⟩
  unfold dR
  exact_mod_cast Finset.card_pos.mpr ⟨U, hmem⟩

private theorem mean_lt_rank_next
    {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (j : ℕ) (hjn : j < Fintype.card α)
    (hdj : 0 < dR adj j)
    (hdnext : 0 < dR adj (j + 1)) :
    critMean adj (j + 1) < ((j : ℝ) + 1) := by
  classical
  have hrank (k : ℕ) :
      GapThreeGraphLevelSynthesisAudit.domRank adj k = domRank adj k := by
    ext S
    simp only [GapThreeGraphLevelSynthesisAudit.domRank, domRank,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hcrit (S : Finset α) :
      GapThreeGraphLevelSynthesisAudit.domCritical adj S = domCritical adj S := by
    ext x
    simp only [GapThreeGraphLevelSynthesisAudit.domCritical, domCritical,
      Finset.mem_filter]
    rfl
  have hinc := GapThreeGraphLevelSynthesisAudit.graph_domination_lemma3_identity
    adj (j + 1) (by omega)
  have hinc' :
      (∑ U ∈ domRank adj (j + 1), (domCritical adj U).card) +
        (Fintype.card α - j) * (domRank adj j).card =
          (domRank adj (j + 1)).card * (j + 1) := by
    simpa [hrank, hcrit] using hinc
  have hc : critSum adj (j + 1) + (((Fintype.card α - j : ℕ) : ℝ) * dR adj j) =
      dR adj (j + 1) * ((j : ℝ) + 1) := by
    have hreal := congrArg (fun z : ℕ => (z : ℝ)) hinc'
    simpa [critSum, dR, Nat.cast_sum, Nat.cast_mul, Nat.cast_add] using hreal
  have hnpos : (0 : ℝ) < ((Fintype.card α - j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hjn)
  have hprod : (0 : ℝ) < ((Fintype.card α - j : ℕ) : ℝ) * dR adj j :=
    mul_pos hnpos hdj
  unfold critMean
  apply (div_lt_iff₀ hdnext).mpr
  nlinarith

private theorem mean_ge_forest_lower
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic)
    (γ : ℕ)
    (hγmin : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (j : ℕ) (hdj : 0 < dR G.Adj j) :
    2 * (γ : ℝ) - (j : ℝ) ≤ critMean G.Adj j := by
  classical
  have hmin' : ∀ S : Finset α,
      GapThreeCriticalConflictCount.IsDominating G.Adj S → γ ≤ S.card := by
    intro S hs
    apply hγmin
    simpa only [IsDominating, GapThreeCriticalConflictCount.IsDominating] using hs
  have hb := GapThreeForestConflictCount.forest_critical_inequality
    G hforest γ hmin'
  have hs : ∀ S ∈ domRank G.Adj j,
      2 * (γ : ℝ) - (j : ℝ) ≤ ((domCritical G.Adj S).card : ℝ) := by
    intro S hS
    have hcard : S.card = j := (Finset.mem_filter.mp hS).2.1
    have hdom : IsDominating G.Adj S := (Finset.mem_filter.mp hS).2.2
    have hx : 2 * γ ≤ (domCritical G.Adj S).card + S.card := by
      convert hb S (by
        simpa only [IsDominating, GapThreeCriticalConflictCount.IsDominating] using hdom)
    have hxr : 2 * (γ : ℝ) ≤ ((domCritical G.Adj S).card : ℝ) + (j : ℝ) := by
      exact_mod_cast (hcard ▸ hx)
    linarith
  have hsum := Finset.sum_le_sum hs
  have hbound : (2 * (γ : ℝ) - (j : ℝ)) * dR G.Adj j ≤ critSum G.Adj j := by
    have hsum' : 2 * (γ : ℝ) * dR G.Adj j ≤
        critSum G.Adj j + (j : ℝ) * dR G.Adj j := by
      simpa [critSum, dR, Finset.sum_const, nsmul_eq_mul,
        mul_comm, mul_left_comm, mul_assoc] using hsum
    linarith
  unfold critMean
  exact (le_div_iff₀ hdj).mpr (by nlinarith)

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
  have hdj : 0 < dR G.Adj j :=
    rank_pos G.Adj S0 hS0 j (by omega) (by omega)
  have hdnext : 0 < dR G.Adj (j + 1) :=
    rank_pos G.Adj S0 hS0 (j + 1) (by omega) (by omega)
  have hlow := mean_ge_forest_lower G hforest γ hγmin j hdj
  have hhi := mean_lt_rank_next G.Adj j hjn hdj hdnext
  linarith

end FinalVerificationJumpBound
