import Mathlib
import domination_gap3.FinalVerificationP24TopTwoCandidate
import domination_gap3.FinalVerificationP24TopAlgebraCandidate

/-! P24 fixed target: binomial conversion, leaf count, full coefficient bound
and necessary condition for equality in any connected graph of order >= 5. -/

namespace FinalVerificationP24IntegerBound

open FinalVerificationP24TopTwo FinalVerificationP24TreeLeaves
open FinalVerificationP24GraphBridge GapThreeGraphConnectionAudit

theorem real_choose_three (n : ℕ) :
    ((n.choose 3 : ℕ) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  sorry

theorem connected_leaves_card_le_n_minus_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hn : 3 ≤ Fintype.card α) :
    (leafVertices G).card ≤ Fintype.card α - 1 := by
  sorry

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
  sorry

end FinalVerificationP24IntegerBound
