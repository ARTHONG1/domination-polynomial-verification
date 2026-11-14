import domination_gap3.ForestConflictLeafBridgeCandidate
import domination_gap3.CriticalConflictCandidate
import domination_gap3.CriticalConflictCountCandidate

namespace GapThreeForestConflictCount

open GapThreeForestAcyclic

noncomputable instance dominating_decidable {α : Type*} (G : SimpleGraph α) :
    DecidablePred (GapThreeCriticalConflictCount.IsDominating G.Adj) :=
  Classical.decPred _

/-- Each newly critical vertex after removing v is a neighbor of v in the
critical-conflict graph. -/
theorem newly_critical_adj {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) (v : Removable G S) (x : α)
    (hx : x ∈ GapThreeCriticalConflictCount.conflictNeighbors G.Adj S v.val) :
    ∃ vx : Removable G S, vx.val = x ∧ (conflictGraph G S).Adj v vx := by
  classical
  obtain ⟨hxS, hxne, hxrem, hxdouble⟩ := Finset.mem_filter.mp hx
  have hxdom : GapThreeCriticalConflict.IsDominating G.Adj (S.erase x) := by
    simpa only [GapThreeCriticalConflict.IsDominating,
      GapThreeCriticalConflictCount.IsDominating] using hxrem
  have hvdom : GapThreeCriticalConflict.IsDominating G.Adj (S.erase v.val) := by
    simpa only [GapThreeCriticalConflict.IsDominating,
      GapThreeForestAcyclic.IsDominating] using v.property.2
  have hdouble : ¬ GapThreeCriticalConflict.IsDominating G.Adj
      ((S.erase v.val).erase x) := by
    simpa only [GapThreeCriticalConflict.IsDominating,
      GapThreeCriticalConflictCount.IsDominating] using hxdouble
  obtain ⟨w, hw⟩ := (GapThreeCriticalConflict.two_removals_witness
    G.Adj S x v.val hxS v.property.1 hxne hxdom hvdom).mp hdouble
  have hw' : footprint G S w = ({v.val, x} : Finset α) := by
    simpa [footprint, GapThreeCriticalConflict.footprint, Finset.pair_comm] using hw
  let vx : Removable G S := ⟨x, hxS, by
    simpa only [GapThreeForestAcyclic.IsDominating,
      GapThreeCriticalConflictCount.IsDominating] using hxrem⟩
  refine ⟨vx, rfl, ?_⟩
  exact ⟨hxne.symm, w, hw'⟩

/-- A conflict-graph leaf has at most one newly critical vertex on deletion. -/
theorem conflict_leaf_count {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α)
    [Fintype (Removable G S)] [DecidableRel (conflictGraph G S).Adj]
    (v : Removable G S)
    (hdeg : (conflictGraph G S).degree v ≤ 1) :
    (GapThreeCriticalConflictCount.conflictNeighbors G.Adj S v.val).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨vx, hvx, hadjx⟩ := newly_critical_adj G S v x hx
  obtain ⟨vy, hvy, hadjy⟩ := newly_critical_adj G S v y hy
  have hneighx : vx ∈ (conflictGraph G S).neighborFinset v := by
    simpa only [SimpleGraph.mem_neighborFinset] using hadjx
  have hneighy : vy ∈ (conflictGraph G S).neighborFinset v := by
    simpa only [SimpleGraph.mem_neighborFinset] using hadjy
  have hsame : vx = vy :=
    (Finset.card_le_one.mp hdeg) vx hneighx vy hneighy
  calc
    x = vx.val := hvx.symm
    _ = vy.val := congrArg Subtype.val hsame
    _ = y := hvy

/-- For every finite forest, the critical-count inequality holds for any
dominating set. This reconstructs the already published Lemma 5. -/
theorem forest_critical_inequality {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α)
    (hforest : G.IsAcyclic)
    (γ : ℕ)
    (hγ_min : ∀ S : Finset α,
      GapThreeCriticalConflictCount.IsDominating G.Adj S → γ ≤ S.card) :
    ∀ S : Finset α, GapThreeCriticalConflictCount.IsDominating G.Adj S →
      2 * γ ≤ (GapThreeCriticalConflictCount.critical G.Adj S).card + S.card := by
  classical
  apply GapThreeCriticalConflictCount.lemma5_from_conflict_leaf G.Adj γ hγ_min
  intro S hdom hrem
  letI : Finite (Removable G S) :=
    Finite.of_injective (Subtype.val : Removable G S → α) Subtype.val_injective
  letI : Fintype (Removable G S) := Fintype.ofFinite _
  have hrem' : ∃ v ∈ S, GapThreeForestAcyclic.IsDominating G.Adj (S.erase v) := by
    obtain ⟨v, hv, hvdom⟩ := hrem
    exact ⟨v, hv, by
      simpa only [GapThreeForestAcyclic.IsDominating,
        GapThreeCriticalConflictCount.IsDominating] using hvdom⟩
  obtain ⟨v, hdeg⟩ := GapThreeConflictLeaf.exists_low_degree_removable G S hforest hrem'
  exact ⟨v.val, v.property.1, (by
    simpa only [GapThreeCriticalConflictCount.IsDominating,
      GapThreeForestAcyclic.IsDominating] using v.property.2),
    conflict_leaf_count G S v hdeg⟩

end GapThreeForestConflictCount
