import Mathlib

namespace GapThreeForestLowDegree

/-- Every nonempty finite forest has a vertex with at most one neighbor. -/
theorem forest_has_low_degree {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hforest : G.IsAcyclic) :
    ∃ v : V, G.degree v ≤ 1 := by
  classical
  by_cases hsub : Subsingleton V
  · letI : Subsingleton V := hsub
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨v, by simp⟩
  · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨T, hGT, hmax⟩ :=
      SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
        (G := (⊤ : SimpleGraph V)) le_top hforest
    have hmax' : Maximal SimpleGraph.IsAcyclic T := by
      simpa using hmax
    have htree : T.IsTree := SimpleGraph.maximal_isAcyclic_iff_isTree.mp hmax'
    obtain ⟨v, hv⟩ := htree.exists_vert_degree_one_of_nontrivial
    exact ⟨v, (G.degree_le_of_le hGT).trans hv.le⟩

end GapThreeForestLowDegree
