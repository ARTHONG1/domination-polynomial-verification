import Mathlib

namespace GapThreeForestAcyclic

def IsDominating {α : Type*} (adj : α → α → Prop) (S : Finset α) : Prop :=
  ∀ w : α, w ∈ S ∨ ∃ u ∈ S, adj w u

noncomputable def footprint {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) (w : α) : Finset α := by
  classical
  exact S.filter (fun u => w = u ∨ G.Adj w u)

def Removable {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) :=
  {x : α // x ∈ S ∧ IsDominating G.Adj (S.erase x)}

noncomputable def conflictGraph {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) : SimpleGraph (Removable G S) where
  Adj x y := x.val ≠ y.val ∧
    ∃ w : α, footprint G S w = ({x.val, y.val} : Finset α)
  symm := by
    intro x y h
    obtain ⟨hxy, w, hw⟩ := h
    refine ⟨hxy.symm, w, ?_⟩
    simpa only [Finset.pair_comm] using hw
  loopless := by
    intro x hx
    exact hx.1 rfl

private theorem witness_internal_edge {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) (w x y : α)
    (hxy : x ≠ y)
    (hw : footprint G S w = ({x, y} : Finset α))
    (hws : w ∈ S) : G.Adj x y := by
  classical
  have hmem : w ∈ footprint G S w :=
    Finset.mem_filter.mpr ⟨hws, Or.inl rfl⟩
  rw [hw] at hmem
  have heq : w = x ∨ w = y := by simpa using hmem
  rcases heq with heq | heq
  · have hy : y ∈ footprint G S w := by rw [hw]; simp
    rcases (Finset.mem_filter.mp hy).2 with hyx | hadj
    · exact (hxy (heq.symm.trans hyx)).elim
    · simpa [heq] using hadj
  · have hx : x ∈ footprint G S w := by rw [hw]; simp
    rcases (Finset.mem_filter.mp hx).2 with hxy' | hadj
    · exact (hxy (hxy'.symm.trans heq)).elim
    · exact G.symm (by simpa [heq] using hadj)

private theorem witness_external_two_edges {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) (w x y : α)
    (hw : footprint G S w = ({x, y} : Finset α))
    (hws : w ∉ S) : G.Adj x w ∧ G.Adj w y := by
  classical
  have hx : x ∈ footprint G S w := by rw [hw]; simp
  have hy : y ∈ footprint G S w := by rw [hw]; simp
  obtain ⟨hxS, hxW⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyS, hyW⟩ := Finset.mem_filter.mp hy
  have hwx : G.Adj w x := hxW.resolve_left (fun h => hws (h ▸ hxS))
  have hwy : G.Adj w y := hyW.resolve_left (fun h => hws (h ▸ hyS))
  exact ⟨G.symm hwx, hwy⟩

/-- The one- or two-edge route associated with a chosen footprint witness. -/
noncomputable def witnessRoute {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) (x y w : α) (hxy : x ≠ y)
    (hw : footprint G S w = ({x, y} : Finset α)) : G.Walk x y := by
  classical
  by_cases hws : w ∈ S
  · exact .cons (witness_internal_edge G S w x y hxy hw hws) .nil
  · exact .cons (witness_external_two_edges G S w x y hw hws).1
        (.cons (witness_external_two_edges G S w x y hw hws).2 .nil)

private theorem witnessRoute_edges {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) (x y w : α) (hxy : x ≠ y)
    (hw : footprint G S w = ({x, y} : Finset α)) :
    (witnessRoute G S x y w hxy hw).edges =
      if w ∈ S then [s(x,y)] else [s(x,w),s(w,y)] := by
  classical
  by_cases hws : w ∈ S
  · simp [witnessRoute, hws, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]
  · simp [witnessRoute, hws, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]

private theorem pair_from_same_witness {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) (x y z w : α)
    (hxy : x ≠ y)
    (h1 : footprint G S w = ({x, y} : Finset α))
    (h2 : footprint G S w = ({y, z} : Finset α)) : x = z := by
  have hsets : ({x, y} : Finset α) = {y, z} := h1.symm.trans h2
  have hx : x ∈ ({y, z} : Finset α) := by rw [← hsets]; simp
  rcases Finset.mem_insert.mp hx with h | h
  · exact (hxy h).elim
  · simpa using h

/-- Each expanded conflict edge has no immediate retracing of an original edge. -/
private theorem witnessRoute_chain {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) (x y w : α) (hxy : x ≠ y)
    (hw : footprint G S w = ({x, y} : Finset α)) :
    List.IsChain (· ≠ ·) (witnessRoute G S x y w hxy hw).edges := by
  classical
  rw [witnessRoute_edges]
  by_cases hws : w ∈ S
  · simp [hws]
  · have hxw : G.Adj x w := (witness_external_two_edges G S w x y hw hws).1
    simp only [if_neg hws, List.isChain_cons_cons, List.isChain_singleton, and_true]
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hxw.ne h1
    · exact hxy h1

/-- The terminal edge of one expanded conflict edge differs from the initial
edge of the next, unless the original conflict walk immediately backtracks. -/
private theorem witnessRoute_boundary {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) (x y z u v : α)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hu : footprint G S u = ({x, y} : Finset α))
    (hv : footprint G S v = ({y, z} : Finset α)) :
    ∀ a ∈ (witnessRoute G S x y u hxy hu).edges.getLast?,
    ∀ b ∈ (witnessRoute G S y z v hyz hv).edges.head?, a ≠ b := by
  classical
  rw [witnessRoute_edges, witnessRoute_edges]
  have hxS : x ∈ S := by
    have h : x ∈ footprint G S u := by rw [hu]; simp
    exact (Finset.mem_filter.mp h).1
  have hyS : y ∈ S := by
    have h : y ∈ footprint G S u := by rw [hu]; simp
    exact (Finset.mem_filter.mp h).1
  have hzS : z ∈ S := by
    have h : z ∈ footprint G S v := by rw [hv]; simp
    exact (Finset.mem_filter.mp h).1
  by_cases hus : u ∈ S <;> by_cases hvs : v ∈ S
  · simp only [if_pos hus, if_pos hvs, List.getLast?_singleton,
        List.head?_singleton, Option.mem_some_iff]
    intro a ha b hb
    subst a; subst b
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hxy h
    · exact hxz h
  · simp only [if_pos hus, if_neg hvs, List.getLast?_singleton,
        List.head?_cons, Option.mem_some_iff]
    intro a ha b hb
    subst a; subst b
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hxy h
    · exact hvs (h ▸ hxS)
  · simp only [if_neg hus, if_pos hvs, List.getLast?_cons,
        List.head?_singleton, Option.mem_some_iff]
    intro a ha b hb
    subst a; subst b
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hus (h ▸ hyS)
    · exact hus (h ▸ hzS)
  · simp only [if_neg hus, if_neg hvs, List.getLast?_cons,
        List.head?_cons, Option.mem_some_iff]
    intro a ha b hb
    subst a; subst b
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hus (h ▸ hyS)
    · have heq : u = v := h
      exact hxz (pair_from_same_witness G S x y z v hxy (by simpa [heq] using hu) hv)

/-- A witness gives an actual walk in G representing a single conflict edge. -/
noncomputable def edgeLift {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α)
    {x y : Removable G S}
    (h : (conflictGraph G S).Adj x y) : G.Walk x.val y.val :=
  witnessRoute G S x.val y.val (Classical.choose h.2) h.1 (Classical.choose_spec h.2)

/-- Every finite walk in the conflict graph expands to a G-walk. -/
noncomputable def walkLift {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α) :
    {x y : Removable G S} →
    (conflictGraph G S).Walk x y → G.Walk x.val y.val
  | _, _, .nil => .nil
  | _, _, .cons h tail => (edgeLift G S h).append (walkLift G S tail)

private theorem edgeLift_chain {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α)
    {x y : Removable G S} (h : (conflictGraph G S).Adj x y) :
    List.IsChain (· ≠ ·) (edgeLift G S h).edges := by
  classical
  exact witnessRoute_chain G S x.val y.val (Classical.choose h.2)
    h.1 (Classical.choose_spec h.2)

private theorem edgeLift_edges_ne_nil {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α)
    {x y : Removable G S} (h : (conflictGraph G S).Adj x y) :
    (edgeLift G S h).edges ≠ [] := by
  classical
  dsimp [edgeLift]
  rw [witnessRoute_edges]
  split_ifs <;> simp

private theorem edgeLift_boundary {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α)
    {x y z : Removable G S}
    (h : (conflictGraph G S).Adj x y)
    (h' : (conflictGraph G S).Adj y z)
    (hxz : x.val ≠ z.val) :
    ∀ a ∈ (edgeLift G S h).edges.getLast?,
    ∀ b ∈ (edgeLift G S h').edges.head?, a ≠ b := by
  classical
  exact witnessRoute_boundary G S x.val y.val z.val
    (Classical.choose h.2) (Classical.choose h'.2) h.1 h'.1 hxz
    (Classical.choose_spec h.2) (Classical.choose_spec h'.2)

private theorem walkLift_chain {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α)
    {x y : Removable G S} (c : (conflictGraph G S).Walk x y)
    (hc : List.IsChain (· ≠ ·) c.edges) :
    List.IsChain (· ≠ ·) (walkLift G S c).edges := by
  classical
  induction c with
  | nil => simp [walkLift]
  | @cons x y z h tail ih =>
      have htail : List.IsChain (· ≠ ·) tail.edges := by
        have h' := (List.isChain_cons.mp (by simpa [SimpleGraph.Walk.edges_cons] using hc)).2
        simpa using h'
      have ih' := ih htail
      rw [walkLift, SimpleGraph.Walk.edges_append]
      apply List.IsChain.append (edgeLift_chain G S h) ih'
      cases tail with
      | nil => simp [walkLift]
      | @cons y z t h' rest =>
          have hne : (edgeLift G S h').edges ≠ [] := edgeLift_edges_ne_nil G S h'
          have hpair : (s(x, y) : Sym2 (Removable G S)) ≠ s(y, z) := by
            have hp := (List.isChain_cons_cons.mp hc).1
            change (s(x, y) : Sym2 (Removable G S)) ≠ s(y, z) at hp
            exact hp
          have hxz : x.val ≠ z.val := by
            intro heq
            apply hpair
            have hz : x = z := Subtype.ext heq
            rw [← hz]
            exact Sym2.eq_swap
          simpa [walkLift, SimpleGraph.Walk.edges_append,
            List.head?_append_of_ne_nil _ hne] using
            (edgeLift_boundary G S h h' hxz)

private theorem walkLift_cons_edges_ne_nil {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α)
    {x y z : Removable G S} (h : (conflictGraph G S).Adj x y)
    (tail : (conflictGraph G S).Walk y z) :
    (walkLift G S (.cons h tail)).edges ≠ [] := by
  intro hh
  simp only [walkLift, SimpleGraph.Walk.edges_append] at hh
  exact edgeLift_edges_ne_nil G S h (List.append_eq_nil_iff.mp hh).1

/-- A conflict cycle cannot lift to a nonempty nonbacktracking closed walk in a forest. -/
theorem forest_conflict_acyclic {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (S : Finset α)
    (hforest : G.IsAcyclic) : (conflictGraph G S).IsAcyclic := by
  intro x c hc
  have hcchain : List.IsChain (· ≠ ·) c.edges :=
    hc.1.1.edges_nodup.isChain
  have hpath : (walkLift G S c).IsPath :=
    (hforest.isPath_iff_isChain _).2 (walkLift_chain G S c hcchain)
  have hnil : walkLift G S c = .nil :=
    (SimpleGraph.Walk.isPath_iff_eq_nil _).1 hpath
  cases c with
  | nil => exact hc.ne_nil rfl
  | cons h tail =>
      have hh : (walkLift G S (.cons h tail)).edges = [] := by
        rw [hnil]
        rfl
      exact walkLift_cons_edges_ne_nil G S h tail hh

end GapThreeForestAcyclic
