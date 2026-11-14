import Mathlib
import domination_gap3.GraphConnectionTheoremCandidate

namespace BipartiteCriticalIndependentAudit
open GapThreeGraphConnectionAudit

private lemma exists_private_witness
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (S : Finset α) (hS : IsDominating G.Adj S)
    (x : α) (hx : x ∈ domCritical G.Adj S) :
    ∃ w : α, (w = x ∨ G.Adj w x) ∧
      (∀ u ∈ S, (w = u ∨ G.Adj w u) → u = x) := by
  have hf : ¬ IsDominating G.Adj (S.erase x) :=
    (Finset.mem_filter.mp hx).2
  change ¬ ∀ w : α, w ∈ S.erase x ∨
    ∃ u ∈ S.erase x, G.Adj w u at hf
  obtain ⟨w, hw⟩ := not_forall.mp hf
  have hp : ∀ u ∈ S, (w = u ∨ G.Adj w u) → u = x := by
    intro u hu hcovered
    by_contra hneq
    have hdel : u ∈ S.erase x := Finset.mem_erase.mpr ⟨hneq, hu⟩
    rcases hcovered with hsame | hadj
    · apply hw (Or.inl ?_)
      simpa [hsame] using hdel
    · exact hw (Or.inr ⟨u, hdel, hadj⟩)
  refine ⟨w, ?_, hp⟩
  rcases hS w with hmem | ⟨u, hu, hadj⟩
  · exact Or.inl (hp w hmem (Or.inl rfl))
  · exact Or.inr (by simpa [hp u hu (Or.inr hadj)] using hadj)

theorem bipartite_critical_le_two_independence
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hbi : G.IsBipartite) (S : Finset α)
    (hS : IsDominating G.Adj S) :
    S.card + (domCritical G.Adj S).card ≤ 2 * G.indepNum := by
  classical
  let C := domCritical G.Adj S
  have hCS : C ⊆ S := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  let f : α → α := fun x =>
    if hx : x ∈ C then Classical.choose
      (exists_private_witness G S hS x hx) else x
  have hf (x : α) (hx : x ∈ C) :
      (f x = x ∨ G.Adj (f x) x) ∧
      (∀ u ∈ S, (f x = u ∨ G.Adj (f x) u) → u = x) := by
    dsimp [f]
    rw [dif_pos hx]
    exact Classical.choose_spec (exists_private_witness G S hS x hx)
  have hfself (x : α) (hx : x ∈ C) (hin : f x ∈ S) : f x = x :=
    (hf x hx).2 (f x) hin (Or.inl rfl)
  have hfout (x : α) (hx : x ∈ C) (hne : f x ≠ x) : f x ∉ S :=
    fun hin => hne (hfself x hx hin)
  have hfinj : Set.InjOn f (↑C : Set α) := by
    intro x hx y hy hxy
    have hcovered : f y = x ∨ G.Adj (f y) x := by
      simpa only [hxy] using (hf x hx).1
    exact (hf y hy).2 x (hCS hx) hcovered
  let E := C.filter (fun x => f x = x)
  let C1 := C.filter (fun x => f x ≠ x)
  let W := C1.image f
  let B := S ∪ W
  have hEsub : E ⊆ S := by
    intro x hx
    exact hCS (Finset.mem_filter.mp hx).1
  have hWout : ∀ y ∈ W, y ∉ S := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hfout x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  have hisol : ∀ x ∈ E, ∀ y ∈ B, ¬G.Adj x y := by
    intro x hx y hy hadj
    have hxC := (Finset.mem_filter.mp hx).1
    have hxfix := (Finset.mem_filter.mp hx).2
    rcases Finset.mem_union.mp hy with hyS | hyW
    · have hyeq : y = x := (hf x hxC).2 y hyS
        (Or.inr (by simpa [hxfix] using hadj))
      exact (G.ne_of_adj hadj) hyeq.symm
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hyW
      have hzC := (Finset.mem_filter.mp hz).1
      have hzneq := (Finset.mem_filter.mp hz).2
      have hxeq : x = z := (hf z hzC).2 x (hEsub hx)
        (Or.inr hadj.symm)
      exact hzneq (by simpa [hxeq] using hxfix)
  obtain ⟨c⟩ := hbi
  have hcolor : ∀ {x y : α}, G.Adj x y → c x ≠ c y := by
    intro x y hxy
    exact c.map_rel' hxy
  have htwo (x : α) : c x = (0 : Fin 2) ∨ c x = (1 : Fin 2) := by
    have hval : (c x).val = 0 ∨ (c x).val = 1 := by omega
    rcases hval with h0 | h1
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h1)
  let I (i : Fin 2) :=
    B.filter (fun x => c x = i) ∪ E.filter (fun x => c x ≠ i)
  have hindep (i : Fin 2) : G.IsIndepSet (↑(I i) : Set α) := by
    intro x hx y hy hxy hadj
    have hx' : x ∈ I i := hx
    have hy' : y ∈ I i := hy
    rcases Finset.mem_union.mp hx' with hxB | hxE
    · rcases Finset.mem_union.mp hy' with hyB | hyE
      · exact (hcolor hadj)
          ((Finset.mem_filter.mp hxB).2.trans (Finset.mem_filter.mp hyB).2.symm)
      · exact hisol y (Finset.mem_filter.mp hyE).1 x
          (Finset.mem_filter.mp hxB).1 hadj.symm
    · have hxE' := (Finset.mem_filter.mp hxE).1
      exact hisol x hxE' y (by
        rcases Finset.mem_union.mp hy' with hyB | hyE
        · exact (Finset.mem_filter.mp hyB).1
        · exact Finset.mem_union_left W (hEsub (Finset.mem_filter.mp hyE).1)) hadj
  have hIcard (i : Fin 2) :
      (I i).card = (B.filter (fun x => c x = i)).card +
        (E.filter (fun x => c x ≠ i)).card := by
    apply Finset.card_union_of_disjoint
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2
  have hWcard : W.card = C1.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    exact hfinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
  have hSW : Disjoint S W := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hWout x hy hx
  have hBcard : B.card = S.card + W.card :=
    Finset.card_union_of_disjoint hSW
  have hCE : E.card + C1.card = C.card := by
    have hcu : E ∪ C1 = C := by
      ext x
      simp only [E, C1, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        by_cases h : f x = x
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
    have hcd : Disjoint E C1 := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      change x ∈ C.filter (fun z => f z = z) at hx
      change x ∈ C.filter (fun z => f z ≠ z) at hy
      exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2
    rw [← Finset.card_union_of_disjoint hcd, hcu]
  have hpart (F : Finset α) :
      (F.filter (fun x => c x = 0)).card +
        (F.filter (fun x => c x = 1)).card = F.card := by
    have hu : F.filter (fun x => c x = 0) ∪
        F.filter (fun x => c x = 1) = F := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        rcases htwo x with hc0 | hc1
        · exact Or.inl ⟨hx, hc0⟩
        · exact Or.inr ⟨hx, hc1⟩
    have hd : Disjoint (F.filter (fun x => c x = 0))
        (F.filter (fun x => c x = 1)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      have h0 := (Finset.mem_filter.mp hx).2
      have h1 := (Finset.mem_filter.mp hy).2
      exact (by decide : (0 : Fin 2) ≠ 1) (h0.symm.trans h1)
    rw [← Finset.card_union_of_disjoint hd, hu]
  have he0 : E.filter (fun x => c x ≠ 0) = E.filter (fun x => c x = 1) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hn⟩
      rcases htwo x with h0 | h1
      · exact False.elim (hn h0)
      · exact ⟨hx, h1⟩
    · rintro ⟨hx, h1⟩
      exact ⟨hx, by simp [h1]⟩
  have he1 : E.filter (fun x => c x ≠ 1) = E.filter (fun x => c x = 0) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hn⟩
      rcases htwo x with h0 | h1
      · exact ⟨hx, h0⟩
      · exact False.elim (hn h1)
    · rintro ⟨hx, h0⟩
      exact ⟨hx, by simp [h0]⟩
  have hsum : (I 0).card + (I 1).card = S.card + C.card := by
    rw [hIcard, hIcard, he0, he1]
    have hbp := hpart B
    have hep := hpart E
    omega
  have h0 : (I 0).card ≤ G.indepNum := (hindep 0).card_le_indepNum
  have h1 : (I 1).card ≤ G.indepNum := (hindep 1).card_le_indepNum
  change S.card + C.card ≤ 2 * G.indepNum
  omega

end BipartiteCriticalIndependentAudit
