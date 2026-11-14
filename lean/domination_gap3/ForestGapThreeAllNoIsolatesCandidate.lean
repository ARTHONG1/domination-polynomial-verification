import Mathlib
import domination_gap3.ForestGapThreeLargeNoMatchingCandidate

namespace ForestGapThreeAllNoIsolatesAudit
open GapThreeGraphConnectionAudit

private theorem minimal_dominating_complement_dominating
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (hnoisolates : ∀ v, ∃ u, G.Adj v u)
    (M : Finset α) (hM : IsDominating G.Adj M)
    (hMminimal : ∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x)) :
    IsDominating G.Adj (Finset.univ \ M) := by
  classical
  have houtside : ∀ x ∈ M, ∃ u, u ∉ M ∧ G.Adj x u := by
    intro x hx
    by_contra hn
    have hinside : ∀ u, G.Adj x u → u ∈ M := by
      intro u hadj
      by_contra hu
      exact hn ⟨u, hu, hadj⟩
    apply hMminimal x hx
    intro v
    by_cases hvM : v ∈ M
    · by_cases hvx : v = x
      · subst v
        obtain ⟨u, hadj⟩ := hnoisolates x
        have huM := hinside u hadj
        have hux : u ≠ x := by
          intro hux
          subst u
          exact G.irrefl hadj
        exact Or.inr ⟨u, Finset.mem_erase.mpr ⟨hux, huM⟩, hadj⟩
      · exact Or.inl (Finset.mem_erase.mpr ⟨hvx, hvM⟩)
    · rcases hM v with hvm | ⟨u, huM, hadj⟩
      · exact (hvM hvm).elim
      · have hux : u ≠ x := by
          intro hux
          subst u
          exact hvM (hinside v hadj.symm)
        exact Or.inr ⟨u, Finset.mem_erase.mpr ⟨hux, huM⟩, hadj⟩
  intro v
  by_cases hvM : v ∈ M
  · obtain ⟨u, huM, hadj⟩ := houtside v hvM
    exact Or.inr ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huM⟩, hadj⟩
  · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvM⟩)

private theorem rank_upper_choose
    {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (k : ℕ) :
    (domRank adj k).card ≤ (Fintype.card α).choose k := by
  have hs : domRank adj k ⊆ Finset.powersetCard k (Finset.univ : Finset α) := by
    intro S hS
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_filter.mp hS).2.1⟩
  simpa [Finset.card_powersetCard] using Finset.card_le_card hs

private theorem rank_lower_singleton
    {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (x : α) (hx : IsDominating adj {x}) (k : ℕ) (hk : 1 ≤ k) :
    ((Fintype.card α - 1).choose (k - 1)) ≤ (domRank adj k).card
      := by
  classical
  let choices := Finset.powersetCard (k - 1) (Finset.univ.erase x)
  have hxin : ∀ U ∈ choices, x ∉ U := by
    intro U hU hxU
    have := (Finset.mem_powersetCard.mp hU).1 hxU
    simpa using this
  have hinj : Set.InjOn (fun U : Finset α => insert x U) (↑choices : Set (Finset α)) := by
    intro U hU V hV hUV
    have hUerase := congrArg (fun S : Finset α => S.erase x) hUV
    simpa [Finset.erase_insert, hxin U hU, hxin V hV] using hUerase
  have hsub : choices.image (fun U : Finset α => insert x U) ⊆ domRank adj k := by
    intro S hS
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hS
    have hUcard := (Finset.mem_powersetCard.mp hU).2
    simp only [domRank, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rw [Finset.card_insert_of_notMem (hxin U hU), hUcard]
      omega
    · intro v
      rcases hx v with hv | ⟨u, hu, hadj⟩
      · exact Or.inl (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hv)))
      · have hux : u = x := Finset.mem_singleton.mp hu
        subst u
        exact Or.inr ⟨x, Finset.mem_insert_self _ _, hadj⟩
  have hchoice : choices.card = (Fintype.card α - 1).choose (k - 1) := by
    simp [choices, Finset.card_powersetCard, Finset.card_erase_of_mem]
  calc
    (Fintype.card α - 1).choose (k - 1) = choices.card := hchoice.symm
    _ = (choices.image (fun U : Finset α => insert x U)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (domRank adj k).card := Finset.card_le_card hsub

private theorem rank_zero_after_order
    {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (k : ℕ) (hk : Fintype.card α < k) : dR adj k = 0 := by
  have hempty : domRank adj k = ∅ := by
    ext S
    constructor
    · intro hS
      have hcard := (Finset.mem_filter.mp hS).2.1
      have hle : S.card ≤ Fintype.card α := by
        simpa using (Finset.card_le_card (Finset.subset_univ S))
      omega
    · simp
  simp [dR, hempty]

private theorem singleton_five_unimodal
    {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (hn : Fintype.card α = 5)
    (x : α) (hx : IsDominating adj {x}) :
    ∃ m : ℕ, (∀ k < m, dR adj k ≤ dR adj (k + 1)) ∧
      (∀ k ≥ m, dR adj (k + 1) ≤ dR adj k) := by
  classical
  letI : DecidablePred (GapThreeGraphLevelSynthesisAudit.IsDominating adj) :=
    inferInstanceAs (DecidablePred (IsDominating adj))
  have hrank (j : ℕ) :
      GapThreeGraphLevelSynthesisAudit.domRank adj j = domRank adj j := by
    ext S
    simp only [GapThreeGraphLevelSynthesisAudit.domRank, domRank,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hcrit (S : Finset α) :
      GapThreeGraphLevelSynthesisAudit.domCritical adj S = domCritical adj S := by
    ext y
    simp only [GapThreeGraphLevelSynthesisAudit.domCritical, domCritical,
      Finset.mem_filter]
    rfl
  have h01nat : (domRank adj 0).card ≤ (domRank adj 1).card := by
    have h := GapThreeGraphLevelSynthesisAudit.graph_domination_lemma3_identity
      adj 1 (by omega)
    simp only [hrank, hcrit, hn, Nat.sub_zero, Nat.mul_one, Nat.zero_add,
      Nat.reduceSubDiff, Nat.reduceMul, Nat.reduceAdd] at h
    omega
  have h12nat : (domRank adj 1).card ≤ (domRank adj 2).card := by
    have h := GapThreeGraphLevelSynthesisAudit.graph_domination_lemma3_identity
      adj 2 (by omega)
    simp only [hrank, hcrit, hn, Nat.sub_zero, Nat.mul_one, Nat.zero_add,
      Nat.reduceSubDiff, Nat.reduceMul, Nat.reduceAdd] at h
    omega
  have h34nat : (domRank adj 4).card ≤ (domRank adj 3).card := by
    have h3 := rank_lower_singleton adj x hx 3 (by omega)
    have h4 := rank_upper_choose adj 4
    rw [hn] at h3 h4
    norm_num [Nat.choose] at h3 h4
    omega
  have h45nat : (domRank adj 5).card ≤ (domRank adj 4).card := by
    have h4 := rank_lower_singleton adj x hx 4 (by omega)
    have h5 := rank_upper_choose adj 5
    rw [hn] at h4 h5
    norm_num [Nat.choose] at h4 h5
    omega
  have h01 : dR adj 0 ≤ dR adj 1 := by
    change ((domRank adj 0).card : ℝ) ≤ ((domRank adj 1).card : ℝ)
    exact_mod_cast h01nat
  have h12 : dR adj 1 ≤ dR adj 2 := by
    change ((domRank adj 1).card : ℝ) ≤ ((domRank adj 2).card : ℝ)
    exact_mod_cast h12nat
  have h34 : dR adj 4 ≤ dR adj 3 := by
    change ((domRank adj 4).card : ℝ) ≤ ((domRank adj 3).card : ℝ)
    exact_mod_cast h34nat
  have h45 : dR adj 5 ≤ dR adj 4 := by
    change ((domRank adj 5).card : ℝ) ≤ ((domRank adj 4).card : ℝ)
    exact_mod_cast h45nat
  have htail : ∀ k, 3 ≤ k → dR adj (k + 1) ≤ dR adj k := by
    intro k hk
    by_cases hk3 : k = 3
    · subst k
      simpa using h34
    by_cases hk4 : k = 4
    · subst k
      simpa using h45
    have hk5 : 5 ≤ k := by omega
    have hnext : dR adj (k + 1) = 0 :=
      rank_zero_after_order adj (k + 1) (by omega)
    rw [hnext]
    change (0 : ℝ) ≤ ((domRank adj k).card : ℝ)
    positivity
  by_cases h23 : dR adj 2 ≤ dR adj 3
  · refine ⟨3, ?_, htail⟩
    intro k hk
    interval_cases k <;> simpa using (by first | exact h01 | exact h12 | exact h23)
  · refine ⟨2, ?_, ?_⟩
    · intro k hk
      interval_cases k <;> simpa using (by first | exact h01 | exact h12)
    · intro k hk
      by_cases hk2 : k = 2
      · subst k
        exact le_of_not_ge h23
      · exact htail k (by omega)

theorem forest_gap_three_unimodal_no_isolates
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (hforest : G.IsAcyclic) (hnoisolates : ∀ v, ∃ u, G.Adj v u)
    (γ : ℕ) (S0 M : Finset α)
    (hS0 : IsDominating G.Adj S0) (hS0card : S0.card ≤ γ)
    (hγ_min : ∀ S : Finset α, IsDominating G.Adj S → γ ≤ S.card)
    (hM : IsDominating G.Adj M)
    (hMminimal : ∀ x ∈ M, ¬ IsDominating G.Adj (M.erase x))
    (hMcard : M.card = γ + 3)
    (hΓ_max : ∀ N : Finset α, IsDominating G.Adj N →
      (∀ x ∈ N, ¬ IsDominating G.Adj (N.erase x)) → N.card ≤ γ + 3) :
    ∃ m : ℕ, (∀ k < m, dR G.Adj k ≤ dR G.Adj (k + 1)) ∧
      (∀ k ≥ m, dR G.Adj (k + 1) ≤ dR G.Adj k) := by
  classical
  let n := Fintype.card α
  have hcomplement := minimal_dominating_complement_dominating
    G hnoisolates M hM hMminimal
  have hcompcard : γ ≤ (Finset.univ \ M).card := hγ_min _ hcomplement
  have hcompeq : (Finset.univ \ M).card = n - M.card := by
    simp [n, Finset.card_sdiff]
  have hMle : M.card ≤ n := by
    simpa [n] using (Finset.card_le_card (Finset.subset_univ M))
  have hn_lower : 2 * γ + 3 ≤ n := by omega
  by_cases hn_large : γ + 5 ≤ n
  · exact ForestGapThreeLargeNoMatchingAudit.forest_gap_three_large_unimodal
      G hforest γ S0 hS0 hS0card hγ_min hΓ_max hn_large
  · have hγpos : 0 < γ := by
      by_contra hnot
      have hγzero : γ = 0 := by omega
      have hS0empty : S0 = ∅ := Finset.card_eq_zero.mp (by omega)
      have hMpositive : 0 < M.card := by omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hMpositive
      rcases hS0 v with hvS | ⟨u, huS, _⟩
      · simpa [hS0empty] using hvS
      · simpa [hS0empty] using huS
    have hγone : γ = 1 := by omega
    have hn5 : n = 5 := by omega
    have hS0one : S0.card = 1 := by
      have hS0positive : 0 < S0.card := by
        by_contra hzero
        have hS0empty : S0 = ∅ := Finset.card_eq_zero.mp (by omega)
        obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
        rcases hS0 v with hvS | ⟨u, huS, _⟩
        · simpa [hS0empty] using hvS
        · simpa [hS0empty] using huS
      omega
    obtain ⟨x, hxS0⟩ := Finset.card_eq_one.mp hS0one
    subst S0
    exact singleton_five_unimodal G.Adj hn5 x hS0

end ForestGapThreeAllNoIsolatesAudit
