import Mathlib
import domination_gap3.GraphConnectionTheoremCandidate

/-! Proof candidate for the isolate-removal bijection used in the submitted
paper's Lemma 2.3. We start with its exact dominating-set equivalence,
without assuming any enumeration or external certificate. -/

namespace FinalVerificationIsolates
open GapThreeGraphConnectionAudit

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem dominating_iff_isolates_and_restricted
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I S : Finset α)
    (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w) :
    IsDominating G.Adj S ↔
      I ⊆ S ∧
      IsDominating
        (fun (v w : {v : α // v ∉ I}) => G.Adj v.1 w.1)
        (S.subtype (fun v => v ∉ I)) := by
  classical
  constructor
  · intro hd
    constructor
    · intro v hvI
      rcases hd v with hvS | ⟨u, hu, hadj⟩
      · exact hvS
      · exact False.elim ((hI v).mp hvI u hadj)
    · intro v
      rcases hd v.1 with hvS | ⟨u, hu, hadj⟩
      · exact Or.inl (Finset.mem_subtype.mpr hvS)
      · have huI : u ∉ I := by
          intro hcontra
          exact ((hI u).mp hcontra v.1) (G.symm hadj)
        exact Or.inr ⟨⟨u, huI⟩, Finset.mem_subtype.mpr hu, hadj⟩
  · rintro ⟨hIS, hrest⟩ v
    by_cases hvI : v ∈ I
    · exact Or.inl (hIS hvI)
    · rcases hrest ⟨v, hvI⟩ with hvS | ⟨u, huS, hadj⟩
      · exact Or.inl (Finset.mem_subtype.mp hvS)
      · exact Or.inr ⟨u.1, Finset.mem_subtype.mp huS, hadj⟩

private def lift (I : Finset α) (T : Finset {v : α // v ∉ I}) : Finset α :=
  I ∪ T.map (Function.Embedding.subtype _)

theorem lift_subtype (I : Finset α)
    (T : Finset {v : α // v ∉ I}) :
    (lift I T).subtype (fun v => v ∉ I) = T := by
  classical
  ext v
  simp [lift, v.property]

theorem lift_restrict (I S : Finset α) (hIS : I ⊆ S) :
    lift I (S.subtype (fun v => v ∉ I)) = S := by
  classical
  rw [lift, Finset.subtype_map]
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (hI | ⟨hS, _⟩)
    · exact hIS hI
    · exact hS
  · intro hS
    by_cases hI : x ∈ I
    · exact Or.inl hI
    · exact Or.inr ⟨hS, hI⟩

theorem lift_domination_iff
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w)
    (T : Finset {v : α // v ∉ I}) :
    IsDominating G.Adj (lift I T) ↔
      IsDominating
        (fun (v w : {v : α // v ∉ I}) => G.Adj v.1 w.1) T := by
  classical
  rw [dominating_iff_isolates_and_restricted G I (lift I T) hI,
      lift_subtype]
  simp [lift, Finset.subset_union_left]

theorem restricted_card_add_isolates
    (I S : Finset α) (hIS : I ⊆ S) :
    (S.subtype (fun v => v ∉ I)).card + I.card = S.card := by
  classical
  rw [Finset.card_subtype]
  have hfilter : S.filter (fun v => v ∉ I) = S \ I := by
    ext v
    simp
  rw [hfilter]
  exact Finset.card_sdiff_add_card_eq_card hIS

theorem lift_card
    (I : Finset α) (T : Finset {v : α // v ∉ I}) :
    (lift I T).card = T.card + I.card := by
  classical
  have h := restricted_card_add_isolates I (lift I T)
    (Finset.subset_union_left)
  rw [lift_subtype] at h
  omega

noncomputable def reducedRankCard (G : SimpleGraph α) (I : Finset α) (k : ℕ) : ℕ := by
  classical
  exact (domRank (fun (v w : {v : α // v ∉ I}) => G.Adj v.1 w.1) k).card

theorem domination_rank_card_shift
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w)
    (k : ℕ) :
    (domRank G.Adj (k + I.card)).card =
      reducedRankCard G I k := by
  classical
  unfold reducedRankCard
  apply Finset.card_bij (fun S _ => S.subtype (fun v => v ∉ I))
  · intro S hS
    have hSsize : S.card = k + I.card := (Finset.mem_filter.mp hS).2.1
    have hdom : IsDominating G.Adj S := (Finset.mem_filter.mp hS).2.2
    obtain ⟨hIS, hrest⟩ :=
      (dominating_iff_isolates_and_restricted G I S hI).mp hdom
    have hc := restricted_card_add_isolates I S hIS
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by omega, hrest⟩
  · intro S hS U hU heq
    have hdomS : IsDominating G.Adj S := (Finset.mem_filter.mp hS).2.2
    have hdomU : IsDominating G.Adj U := (Finset.mem_filter.mp hU).2.2
    have hIS := (dominating_iff_isolates_and_restricted G I S hI).mp hdomS |>.1
    have hIU := (dominating_iff_isolates_and_restricted G I U hI).mp hdomU |>.1
    calc
      S = lift I (S.subtype (fun v => v ∉ I)) := (lift_restrict I S hIS).symm
      _ = lift I (U.subtype (fun v => v ∉ I)) := by rw [heq]
      _ = U := lift_restrict I U hIU
  · intro T hT
    let S := lift I T
    have hTsize : T.card = k := (Finset.mem_filter.mp hT).2.1
    have hsize : S.card = k + I.card := by
      simpa [S, hTsize] using lift_card I T
    have hdom : IsDominating G.Adj S := by
      apply (lift_domination_iff G I hI T).mpr
      exact (Finset.mem_filter.mp hT).2.2
    refine ⟨S, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsize, hdom⟩
    · exact lift_subtype I T

theorem domination_rank_below_isolates_zero
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w)
    (k : ℕ) (hk : k < I.card) :
    (domRank G.Adj k).card = 0 := by
  classical
  have hempty : domRank G.Adj k = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro S hS
    have hsize : S.card = k := (Finset.mem_filter.mp hS).2.1
    have hdom : IsDominating G.Adj S := (Finset.mem_filter.mp hS).2.2
    have hIS := (dominating_iff_isolates_and_restricted G I S hI).mp hdom |>.1
    have hc := Finset.card_le_card hIS
    omega
  simp [hempty]

def IsWeakUnimodal (a : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, (∀ k < m, a k ≤ a (k + 1)) ∧
    (∀ k ≥ m, a (k + 1) ≤ a k)

theorem weak_unimodal_shift_iff
    (a b : ℕ → ℝ) (r : ℕ)
    (hbelow : ∀ k < r, a k = 0)
    (hshift : ∀ k, a (k + r) = b k)
    (hnonneg : 0 ≤ b 0) :
    IsWeakUnimodal a ↔ IsWeakUnimodal b := by
  constructor
  · rintro ⟨m, hleft, hright⟩
    refine ⟨m - r, ?_, ?_⟩
    · intro k hk
      have hlt : k + r < m := by omega
      calc
        b k = a (k + r) := (hshift k).symm
        _ ≤ a ((k + 1) + r) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hleft (k + r) hlt
        _ = b (k + 1) := hshift (k + 1)
    · intro k hk
      have hge : m ≤ k + r := by omega
      calc
        b (k + 1) = a ((k + 1) + r) := (hshift (k + 1)).symm
        _ ≤ a (k + r) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hright (k + r) hge
        _ = b k := hshift k
  · rintro ⟨m, hleft, hright⟩
    refine ⟨m + r, ?_, ?_⟩
    · intro k hk
      by_cases hkr : k < r
      · rw [hbelow k hkr]
        by_cases hnext : k + 1 < r
        · rw [hbelow (k + 1) hnext]
        · have heq : k + 1 = r := by omega
          rw [heq]
          have hr0 : a r = b 0 := by simpa using hshift 0
          rw [hr0]
          exact hnonneg
      · have hindex : k - r + r = k := by omega
        have hnextindex : (k - r + 1) + r = k + 1 := by omega
        have hlt : k - r < m := by omega
        calc
          a k = b (k - r) :=
            (congrArg a hindex).symm.trans (hshift (k - r))
          _ ≤ b (k - r + 1) := hleft (k - r) hlt
          _ = a (k + 1) :=
            (hshift (k - r + 1)).symm.trans (congrArg a hnextindex)
    · intro k hk
      have hindex : k - r + r = k := by omega
      have hnextindex : (k - r + 1) + r = k + 1 := by omega
      have hge : m ≤ k - r := by omega
      calc
          a (k + 1) = b (k - r + 1) :=
            (congrArg a hnextindex).symm.trans (hshift (k - r + 1))
          _ ≤ b (k - r) := hright (k - r) hge
          _ = a k := (hshift (k - r)).symm.trans (congrArg a hindex)

noncomputable def reducedDR (G : SimpleGraph α) (I : Finset α) (k : ℕ) : ℝ :=
  (reducedRankCard G I k : ℝ)

theorem domination_isolate_unimodal_iff
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w) :
    IsWeakUnimodal (dR G.Adj) ↔ IsWeakUnimodal (reducedDR G I) := by
  classical
  apply weak_unimodal_shift_iff (dR G.Adj) (reducedDR G I) I.card
  · intro k hk
    have hzero := domination_rank_below_isolates_zero G I hI k hk
    simp only [dR, hzero, Nat.cast_zero]
  · intro k
    unfold dR reducedDR
    exact_mod_cast domination_rank_card_shift G I hI k
  · unfold reducedDR
    positivity

theorem restrict_erase
    (I S : Finset α) (v : {v : α // v ∉ I}) :
    (S.erase v.1).subtype (fun u => u ∉ I) =
      (S.subtype (fun u => u ∉ I)).erase v := by
  classical
  ext w
  simp [Finset.mem_subtype, Finset.mem_erase, Subtype.ext_iff]

theorem minimal_domination_iff_restrict
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w)
    (S : Finset α) (hS : IsDominating G.Adj S) :
    (∀ v ∈ S, ¬ IsDominating G.Adj (S.erase v)) ↔
      (∀ v ∈ S.subtype (fun u => u ∉ I),
        ¬ IsDominating
          (fun (w u : {u : α // u ∉ I}) => G.Adj w.1 u.1)
          ((S.subtype (fun u => u ∉ I)).erase v)) := by
  classical
  have hIS := (dominating_iff_isolates_and_restricted G I S hI).mp hS |>.1
  constructor
  · intro hmin v hv hbad
    have hvS : v.1 ∈ S := Finset.mem_subtype.mp hv
    have hIerase : I ⊆ S.erase v.1 := by
      intro u hu
      exact Finset.mem_erase.mpr
        ⟨(fun heq => v.2 (heq ▸ hu)), hIS hu⟩
    have hdomerase : IsDominating G.Adj (S.erase v.1) := by
      apply (dominating_iff_isolates_and_restricted G I (S.erase v.1) hI).mpr
      refine ⟨hIerase, ?_⟩
      simpa only [restrict_erase] using hbad
    exact hmin v.1 hvS hdomerase
  · intro hmin v hvS hbad
    by_cases hvI : v ∈ I
    · have hIerase := (dominating_iff_isolates_and_restricted G I
        (S.erase v) hI).mp hbad |>.1
      exact Finset.notMem_erase v S (hIerase hvI)
    · let v' : {u : α // u ∉ I} := ⟨v, hvI⟩
      have hvT : v' ∈ S.subtype (fun u => u ∉ I) :=
        Finset.mem_subtype.mpr hvS
      have hbadT := (dominating_iff_isolates_and_restricted G I
        (S.erase v) hI).mp hbad |>.2
      change IsDominating
        (fun (w u : {u : α // u ∉ I}) => G.Adj w.1 u.1)
        ((S.erase v).subtype (fun u => u ∉ I)) at hbadT
      rw [show (S.erase v).subtype (fun u => u ∉ I) =
        (S.subtype (fun u => u ∉ I)).erase v' from
          restrict_erase I S v'] at hbadT
      exact hmin v' hvT hbadT

theorem domination_number_isolate_shift
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w)
    (γ : ℕ) (S0 : Finset α)
    (hS0 : IsDominating G.Adj S0) (hS0card : S0.card ≤ γ)
    (hγmin : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card) :
    ∃ T : Finset {v : α // v ∉ I},
      IsDominating (fun v w => G.Adj v.1 w.1) T ∧
      T.card + I.card = γ ∧
      ∀ U : Finset {v : α // v ∉ I},
        IsDominating (fun v w => G.Adj v.1 w.1) U →
        γ ≤ U.card + I.card := by
  classical
  have hS0exact : S0.card = γ := Nat.le_antisymm hS0card (hγmin S0 hS0)
  obtain ⟨hIS, hrest⟩ :=
    (dominating_iff_isolates_and_restricted G I S0 hI).mp hS0
  refine ⟨S0.subtype (fun v => v ∉ I), hrest, ?_, ?_⟩
  · have hc := restricted_card_add_isolates I S0 hIS
    omega
  · intro U hU
    have hdom := (lift_domination_iff G I hI U).mpr hU
    have hbound := hγmin (lift I U) hdom
    have hc := lift_card I U
    omega

theorem upper_domination_number_isolate_shift
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w)
    (Γ : ℕ) (M : Finset α)
    (hM : IsDominating G.Adj M)
    (hMminimal : ∀ v ∈ M, ¬ IsDominating G.Adj (M.erase v))
    (hMcard : M.card = Γ)
    (hΓmax : ∀ N : Finset α, IsDominating G.Adj N →
      (∀ v ∈ N, ¬ IsDominating G.Adj (N.erase v)) → N.card ≤ Γ) :
    ∃ T : Finset {v : α // v ∉ I},
      IsDominating (fun v w => G.Adj v.1 w.1) T ∧
      (∀ v ∈ T,
        ¬ IsDominating (fun w u => G.Adj w.1 u.1) (T.erase v)) ∧
      T.card + I.card = Γ ∧
      ∀ U : Finset {v : α // v ∉ I},
        IsDominating (fun v w => G.Adj v.1 w.1) U →
        (∀ v ∈ U,
          ¬ IsDominating (fun w u => G.Adj w.1 u.1) (U.erase v)) →
        U.card + I.card ≤ Γ := by
  classical
  obtain ⟨hIS, hrest⟩ :=
    (dominating_iff_isolates_and_restricted G I M hI).mp hM
  have hminrest := (minimal_domination_iff_restrict G I hI M hM).mp hMminimal
  refine ⟨M.subtype (fun v => v ∉ I), hrest, hminrest, ?_, ?_⟩
  · have hc := restricted_card_add_isolates I M hIS
    omega
  · intro U hU hminU
    have hdom := (lift_domination_iff G I hI U).mpr hU
    have hmin : ∀ v ∈ lift I U,
        ¬ IsDominating G.Adj ((lift I U).erase v) := by
      apply (minimal_domination_iff_restrict G I hI (lift I U) hdom).mpr
      simpa only [lift_subtype] using hminU
    have hbound := hΓmax (lift I U) hdom hmin
    have hc := lift_card I U
    omega

end FinalVerificationIsolates
