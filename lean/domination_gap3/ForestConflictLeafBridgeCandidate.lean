import domination_gap3.ConflictForestAcyclicCandidate
import domination_gap3.ForestLowDegreeCandidate

namespace GapThreeConflictLeaf

open GapThreeForestAcyclic

/-- In a forest, every nonempty critical-conflict graph has a removable
vertex with at most one conflict neighbor. -/
theorem exists_low_degree_removable {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α)
    [Fintype (Removable G S)] [DecidableRel (conflictGraph G S).Adj]
    (hforest : G.IsAcyclic)
    (hrem : ∃ v ∈ S, IsDominating G.Adj (S.erase v)) :
    ∃ v : Removable G S, (conflictGraph G S).degree v ≤ 1 := by
  classical
  letI : Nonempty (Removable G S) := ⟨⟨hrem.choose, hrem.choose_spec⟩⟩
  exact GapThreeForestLowDegree.forest_has_low_degree
    (conflictGraph G S) (forest_conflict_acyclic G S hforest)

end GapThreeConflictLeaf
