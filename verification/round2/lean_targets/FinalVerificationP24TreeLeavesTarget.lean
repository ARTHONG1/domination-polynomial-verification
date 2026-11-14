import Mathlib
import domination_gap3.FinalVerificationP24GraphBridgeCandidate

/-! Fixed targets: connect actual degree-one leaves and connected graphs to
the already verified graph-level d_(n-3) count bound. -/

namespace FinalVerificationP24TreeLeaves

open FinalVerificationP24GraphBridge GapThreeGraphConnectionAudit

theorem leaf_closed_nbr_card_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) (hdeg : G.degree v = 1) :
    (closedNbr G v).card = 2 := by
  sorry

theorem adjacent_degree_one_vertices_force_card_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (v w : α) (hvw : G.Adj v w)
    (hv : G.degree v = 1) (hw : G.degree w = 1) :
    Fintype.card α ≤ 2 := by
  sorry

theorem distinct_degree_one_closed_nbr
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 3 ≤ Fintype.card α)
    (v w : α) (hv : G.degree v = 1) (hw : G.degree w = 1)
    (hne : v ≠ w) :
    closedNbr G v ≠ closedNbr G w := by
  sorry

noncomputable def leafVertices {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  Finset.univ.filter (fun v => G.degree v = 1)

theorem connected_graph_top_three_count_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    [DecidablePred (IsDominating G.Adj)]
    (hconn : G.Connected) (hn : 5 ≤ Fintype.card α) :
    (domRank G.Adj (Fintype.card α - 3)).card +
      (leafVertices G).card * (Fintype.card α - 2) ≤
      (Fintype.card α).choose 3 + (leafVertices G).card.choose 2 := by
  sorry

end FinalVerificationP24TreeLeaves
