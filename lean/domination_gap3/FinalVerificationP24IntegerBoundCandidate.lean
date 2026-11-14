import Mathlib
import domination_gap3.FinalVerificationP24TopTwoCandidate
import domination_gap3.FinalVerificationP24TopAlgebraCandidate

/-! Submitted Section 7 P24: the fully connected integer coefficient bound
after deriving the exact leaf formulas from the graph's actual domination data. -/

namespace FinalVerificationP24IntegerBound

open FinalVerificationP24TopTwo FinalVerificationP24TreeLeaves
open FinalVerificationP24GraphBridge GapThreeGraphConnectionAudit

theorem real_choose_three (n : ℕ) :
    ((n.choose 3 : ℕ) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hc : (n + 1).choose 3 = n.choose 2 + n.choose 3 := by
        simpa [Nat.add_comm] using (Nat.choose_succ_succ n 2)
      rw [hc, Nat.cast_add, Nat.cast_choose_two ℝ n, ih]
      push_cast
      ring

theorem connected_leaves_card_le_n_minus_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hn : 3 ≤ Fintype.card α) :
    (leafVertices G).card ≤ Fintype.card α - 1 := by
  classical
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI : Nonempty α := inferInstance
  have hne : leafVertices G ≠ (Finset.univ : Finset α) := by
    intro heq
    let v : α := Classical.choice ‹Nonempty α›
    obtain ⟨w, hvw⟩ := hconn.preconnected.exists_adj_of_nontrivial v
    have hv : G.degree v = 1 := by
      have h := Finset.mem_univ v
      rw [← heq] at h
      exact (Finset.mem_filter.mp h).2
    have hw : G.degree w = 1 := by
      have h := Finset.mem_univ w
      rw [← heq] at h
      exact (Finset.mem_filter.mp h).2
    have hb := adjacent_degree_one_vertices_force_card_two G hconn v w hvw hv hw
    omega
  have hproper : leafVertices G ⊂ (Finset.univ : Finset α) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩
  have hcard : (leafVertices G).card < Fintype.card α := by
    simpa using Finset.card_lt_card hproper
  omega

/-- Exact submitted inequality 3n*d_(n-3) <= 2b(b-1),
and the necessary leaf count for equality. No forest assumption is needed. -/
theorem connected_top_coefficient_inequality
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    [DecidablePred (IsDominating G.Adj)]
    (hconn : G.Connected) (hn : 5 ≤ Fintype.card α) :
    3 * (Fintype.card α : ℝ) *
      ((domRank G.Adj (Fintype.card α - 3)).card : ℝ) ≤
      2 * ((domRank G.Adj (Fintype.card α - 2)).card : ℝ) *
      (((domRank G.Adj (Fintype.card α - 2)).card : ℝ) - 1) ∧
    (3 * (Fintype.card α : ℝ) *
      ((domRank G.Adj (Fintype.card α - 3)).card : ℝ) =
      2 * ((domRank G.Adj (Fintype.card α - 2)).card : ℝ) *
      (((domRank G.Adj (Fintype.card α - 2)).card : ℝ) - 1) →
      (leafVertices G).card = Fintype.card α - 1) := by
  classical
  let n : ℕ := Fintype.card α
  let L : ℕ := (leafVertices G).card
  let b : ℕ := (domRank G.Adj (n - 2)).card
  let d : ℕ := (domRank G.Adj (n - 3)).card
  have hL := connected_leaves_card_le_n_minus_one G hconn (by omega)
  have hB : b + L = n.choose 2 :=
    penultimate_domination_coefficient_exact G hconn hn
  have hD : d + L * (n - 2) ≤ n.choose 3 + L.choose 2 :=
    connected_graph_top_three_count_bound G hconn hn
  have hcastN : 5 ≤ (n : ℝ) := by exact_mod_cast hn
  have hcastL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hcastLmax : (L : ℝ) ≤ (n : ℝ) - 1 := by
    have hl : L ≤ n - 1 := hL
    have hlr : (L : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hl
    rw [Nat.cast_sub (by omega : 1 ≤ n)] at hlr
    simpa only [Nat.cast_one] using hlr
  have hcastB : (b : ℝ) = FinalVerificationP24TopAlgebra.b (n : ℝ) (L : ℝ) := by
    have hbReal : (b : ℝ) + (L : ℝ) = (n.choose 2 : ℝ) := by
      exact_mod_cast hB
    rw [Nat.cast_choose_two ℝ n] at hbReal
    unfold FinalVerificationP24TopAlgebra.b
    linarith
  have hcastD : (d : ℝ) ≤ FinalVerificationP24TopAlgebra.u (n : ℝ) (L : ℝ) := by
    have hdReal : (d : ℝ) + (L : ℝ) * ((n - 2 : ℕ) : ℝ) ≤
        (n.choose 3 : ℝ) + (L.choose 2 : ℝ) := by
      exact_mod_cast hD
    rw [real_choose_three, Nat.cast_choose_two ℝ L,
      Nat.cast_sub (by omega : 2 ≤ n)] at hdReal
    unfold FinalVerificationP24TopAlgebra.u
    linarith
  have hAlg := FinalVerificationP24TopAlgebra.top_bound_and_star_equality
    (n : ℝ) (L : ℝ) hcastN hcastL hcastLmax
  have hAbove : 3 * (n : ℝ) * (d : ℝ) ≤
      3 * (n : ℝ) * FinalVerificationP24TopAlgebra.u (n : ℝ) (L : ℝ) :=
    mul_le_mul_of_nonneg_left hcastD (by positivity : 0 ≤ 3 * (n : ℝ))
  have hBound : 3 * (n : ℝ) * (d : ℝ) ≤
      2 * (b : ℝ) * ((b : ℝ) - 1) := by
    rw [hcastB]
    linarith [hAlg.1, hAbove]
  constructor
  · exact hBound
  · intro heq
    have hAEq : 3 * (n : ℝ) * FinalVerificationP24TopAlgebra.u (n : ℝ) (L : ℝ) =
        2 * FinalVerificationP24TopAlgebra.b (n : ℝ) (L : ℝ) *
          (FinalVerificationP24TopAlgebra.b (n : ℝ) (L : ℝ) - 1) := by
      rw [hcastB] at heq
      linarith [hAlg.1, hAbove]
    have hLreal := hAlg.2.mp hAEq
    have hLint : L = n - 1 := by
      have hlin : (L : ℝ) = ((n - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        simpa only [Nat.cast_one] using hLreal
      exact_mod_cast hlin
    exact hLint

end FinalVerificationP24IntegerBound
