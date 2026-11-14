import Mathlib

/-! Second-order finite union bound. This is the combinatorial incidence step
used for the submitted manuscript's coefficient d_(n-3), with no assumption
about truncating after pairwise inclusion/exclusion. -/

namespace FinalVerificationP24Overlap

/-- All 3-subsets containing a fixed (closed-neighborhood) 2-subset. -/
def tripleSupersets {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset α) : Finset (Finset α) :=
  (Finset.univ.powersetCard 3).filter (fun U => P ⊆ U)

/-- A 2-set has precisely n-2 supersets of size 3, for n finite. -/
theorem triple_supersets_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset α) (hP : P.card = 2) :
    (tripleSupersets P).card = Fintype.card α - 2 := by
  classical
  have hcov : tripleSupersets P =
      (Finset.univ \ P).image (fun v => insert v P) := by
    ext U
    constructor
    · intro hU
      have hprops := Finset.mem_filter.mp hU
      have hcardU : U.card = 3 := (Finset.mem_powersetCard.mp hprops.1).2
      have hsub : P ⊆ U := hprops.2
      have hdiff : (U \ P).card = 1 := by
        have hc := Finset.card_sdiff_add_card_eq_card hsub
        omega
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiff
      have hvm : v ∈ U \ P := by rw [hv]; simp
      have hvU : v ∈ U := (Finset.mem_sdiff.mp hvm).1
      have hvP : v ∉ P := (Finset.mem_sdiff.mp hvm).2
      have hsubset : insert v P ⊆ U := Finset.insert_subset hvU hsub
      have hicard : (insert v P).card = 3 := by simp [hvP, hP]
      have heq : insert v P = U :=
        Finset.eq_of_subset_of_card_le hsubset (by omega)
      exact Finset.mem_image.mpr
        ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvP⟩, heq⟩
    · intro hU
      obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hU
      have hvP : v ∉ P := (Finset.mem_sdiff.mp hv).2
      have hicard : (insert v P).card = 3 := by simp [hvP, hP]
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        constructor
        · exact Finset.subset_univ _
        · simpa [← heq] using hicard
      · simpa [← heq] using (Finset.subset_insert v P)
  have hinj : Set.InjOn (fun v : α => insert v P) (↑(Finset.univ \ P)) := by
    intro a ha b hb hab
    have haP : a ∉ P := (Finset.mem_sdiff.mp ha).2
    have haIns : a ∈ insert b P := by
      rw [← (show insert a P = insert b P from hab)]
      exact Finset.mem_insert_self a P
    exact (Finset.mem_insert.mp haIns).resolve_right haP
  rw [hcov, Finset.card_image_of_injOn hinj]
  simpa [Finset.card_sdiff_of_subset (Finset.subset_univ P), hP]

/-- Two different 2-sets fit together in at most one 3-set. -/
theorem distinct_pair_triple_inter_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (P Q : Finset α) (hP : P.card = 2) (hQ : Q.card = 2)
    (hPQ : P ≠ Q) :
    ((tripleSupersets P) ∩ (tripleSupersets Q)).card ≤ 1 := by
  classical
  have hU : 3 ≤ (P ∪ Q).card := by
    by_contra hc
    have hbound : (P ∪ Q).card ≤ 2 := by omega
    have hPunion : P = P ∪ Q :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have hQunion : Q = P ∪ Q :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    exact hPQ (hPunion.trans hQunion.symm)
  apply Finset.card_le_one.mpr
  intro U hUmem V hVmem
  have hUmem' := Finset.mem_inter.mp hUmem
  have hVmem' := Finset.mem_inter.mp hVmem
  have hpU : P ⊆ U := (Finset.mem_filter.mp hUmem'.1).2
  have hqU : Q ⊆ U := (Finset.mem_filter.mp hUmem'.2).2
  have hpV : P ⊆ V := (Finset.mem_filter.mp hVmem'.1).2
  have hqV : Q ⊆ V := (Finset.mem_filter.mp hVmem'.2).2
  have hu3 : U.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hUmem'.1).1).2
  have hv3 : V.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hVmem'.1).1).2
  have heqU : P ∪ Q = U :=
    Finset.eq_of_subset_of_card_le (Finset.union_subset hpU hqU) (by omega)
  have heqV : P ∪ Q = V :=
    Finset.eq_of_subset_of_card_le (Finset.union_subset hpV hqV) (by omega)
  exact heqU.symm.trans heqV

theorem union_lower_from_pairwise_intersections
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (S : Finset ι) (A : ι → Finset α)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (A i ∩ A j).card ≤ 1) :
    (∑ i ∈ S, (A i).card) ≤ (S.biUnion A).card + S.card.choose 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hpair_s : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → (A j ∩ A k).card ≤ 1 := by
        intro j hj k hk hne
        exact hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne
      have hs := ih hpair_s
      have hinter : ((s.biUnion A) ∩ A i).card ≤ s.card := by
        have heq : (s.biUnion A) ∩ A i =
            s.biUnion (fun j => A j ∩ A i) := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_biUnion]
          constructor
          · rintro ⟨⟨j, hj, hx⟩, hxi⟩
            exact ⟨j, hj, ⟨hx, hxi⟩⟩
          · rintro ⟨j, hj, ⟨hx, hxi⟩⟩
            exact ⟨⟨j, hj, hx⟩, hxi⟩
        rw [heq]
        calc
          (s.biUnion (fun j => A j ∩ A i)).card ≤
              ∑ j ∈ s, (A j ∩ A i).card := Finset.card_biUnion_le
          _ ≤ ∑ _j ∈ s, (1 : ℕ) := by
            apply Finset.sum_le_sum
            intro j hj
            have hne : j ≠ i := by
              intro heq
              exact his (heq ▸ hj)
            exact hpair j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s)
              hne
          _ = s.card := by simp
      have hchoose : (s.card + 1).choose 2 = s.card.choose 2 + s.card := by
        simpa [Nat.choose_one_right, Nat.add_comm] using (Nat.choose_succ_succ s.card 1)
      have hcard := Finset.card_union_add_card_inter (s.biUnion A) (A i)
      have hinsert : (insert i s).card = s.card + 1 := by simp [his]
      simp only [Finset.sum_insert his, Finset.biUnion_insert]
      rw [hinsert, hchoose]
      rw [Finset.union_comm (A i) (s.biUnion A)]
      omega

/-- If L distinct 2-sets are forbidden inside 3-subsets, the number of
allowed triples, plus L(n-2), is at most C(n,3)+C(L,2).
This is the integer, division-free version of the submitted upper bound. -/
theorem allowed_triples_bound
    {ι α : Type*} [DecidableEq ι] [Fintype α] [DecidableEq α]
    (S : Finset ι) (P : ι → Finset α)
    (hsize : ∀ i ∈ S, (P i).card = 2)
    (hdistinct : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → P i ≠ P j) :
    (((Finset.univ.powersetCard 3 : Finset (Finset α)) \
      (S.biUnion (fun i => tripleSupersets (P i)))).card +
      S.card * (Fintype.card α - 2) ≤
      (Fintype.card α).choose 3 + S.card.choose 2) := by
  classical
  let A : ι → Finset (Finset α) := fun i => tripleSupersets (P i)
  have hinter : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (A i ∩ A j).card ≤ 1 := by
    intro i hi j hj hne
    exact distinct_pair_triple_inter_le_one (P i) (P j) (hsize i hi)
      (hsize j hj) (hdistinct i hi j hj hne)
  have hsum := union_lower_from_pairwise_intersections S A hinter
  have hsum_eq : (∑ i ∈ S, (A i).card) =
      S.card * (Fintype.card α - 2) := by
    calc
      (∑ i ∈ S, (A i).card) = ∑ _i ∈ S, (Fintype.card α - 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact triple_supersets_card (P i) (hsize i hi)
      _ = S.card * (Fintype.card α - 2) := by simp
  rw [hsum_eq] at hsum
  have hsub : S.biUnion A ⊆
      (Finset.univ.powersetCard 3 : Finset (Finset α)) := by
    intro U hU
    obtain ⟨i, hi, hu⟩ := Finset.mem_biUnion.mp hU
    exact (Finset.mem_filter.mp hu).1
  have hpartition := Finset.card_sdiff_add_card_eq_card hsub
  change (((Finset.univ.powersetCard 3 : Finset (Finset α)) \ S.biUnion A).card +
      S.card * (Fintype.card α - 2) ≤
      (Fintype.card α).choose 3 + S.card.choose 2)
  rw [Finset.card_powersetCard] at hpartition
  simp only [Finset.card_univ] at hpartition
  omega

end FinalVerificationP24Overlap
