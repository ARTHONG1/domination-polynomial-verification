import Mathlib
import domination_gap3.GraphConnectionTheoremCandidate

/-!
Fixed target for submitted manuscript main.tex lines 894--914 (Section 7,
equation (top)): for a tree T with n >= 5,
  c_n-c_(n-1) = -c_(n-1) <= 0,
  c_(n-1)-c_(n-2) <= 1-2/n, equality iff T is a star.
The general connected-simple-graph statements below IMPLY the tree claims,
because every tree is connected. The existing mean definition is that in
GraphConnectionTheoremCandidate, matching the manuscript for d_j > 0.
Do not change the declarations after registering the mathlab proof task.
-/

namespace FinalVerificationP24Final
open GapThreeGraphConnectionAudit

/-- K_(1,n-1) has a centre c adjacent to all other vertices, and every
other vertex has that centre as its only neighbour. -/
def IsStar {α : Type*} (G : SimpleGraph α) : Prop :=
  ∃ c : α, ∀ v : α, v ≠ c →
    G.Adj c v ∧ ∀ w : α, G.Adj v w → w = c

variable {α : Type*} [Fintype α] [DecidableEq α]
  (G : SimpleGraph α) [DecidableRel G.Adj]
  [DecidablePred (IsDominating G.Adj)]

/-- Submitted d_(n-1)=n, used in equation (top). -/
theorem top_minus_one_count (hconn : G.Connected)
    (hn : 2 ≤ Fintype.card α) :
    (domRank G.Adj (Fintype.card α - 1)).card = Fintype.card α := by
  sorry

/-- Submitted c_n=0 and c_(n-1)>=0, hence last jump is nonpositive. -/
theorem last_step (hconn : G.Connected) (hn : 2 ≤ Fintype.card α) :
    critMean G.Adj (Fintype.card α) = 0 ∧
    0 ≤ critMean G.Adj (Fintype.card α - 1) := by
  sorry

/-- Manuscript equation (top), with the actual critical-vertex mean. -/
theorem top_jump_le (hconn : G.Connected) (hn : 5 ≤ Fintype.card α) :
    critMean G.Adj (Fintype.card α - 1) -
      critMean G.Adj (Fintype.card α - 2) ≤
        1 - 2 / (Fintype.card α : ℝ) := by
  sorry

/-- Equation (top) is equality exactly for a star. -/
theorem top_jump_eq_iff_star (hconn : G.Connected)
    (hn : 5 ≤ Fintype.card α) :
    (critMean G.Adj (Fintype.card α - 1) -
      critMean G.Adj (Fintype.card α - 2) =
        1 - 2 / (Fintype.card α : ℝ)) ↔ IsStar G := by
  sorry

end FinalVerificationP24Final
