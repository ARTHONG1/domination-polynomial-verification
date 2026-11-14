import Mathlib
import domination_gap3.FinalVerificationP24TreeLeavesCandidate

/-! The next gap in P24: exact coefficient d_(n-2) by identifying
nondominating two-vertex complements with the closed neighborhoods of leaves. -/

namespace FinalVerificationP24TopTwo

open FinalVerificationP24TreeLeaves
open FinalVerificationP24GraphBridge
open GapThreeGraphConnectionAudit

noncomputable def forbiddenPairs {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) : Finset (Finset α) := by
  classical
  exact (Finset.univ.powersetCard 2).filter
    (fun U => ¬ IsDominating G.Adj (Finset.univ \ U))

theorem nondom_iff_has_closed_nbr
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (D : Finset α) :
    (¬ IsDominating G.Adj D) ↔
      ∃ v : α, closedNbr G v ⊆ (Finset.univ \ D) := by
  classical
  constructor
  · intro hnot
    unfold IsDominating at hnot
    push_neg at hnot
    obtain ⟨v, hvD, hnotadj⟩ := hnot
    refine ⟨v, ?_⟩
    intro u hu
    have hmem : u = v ∨ G.Adj v u := by
      simpa only [closedNbr, Finset.mem_filter, Finset.mem_univ, true_and] using hu
    apply Finset.mem_sdiff.mpr
    constructor
    · simp
    · intro huD
      rcases hmem with heq | hadj
      · exact hvD (heq ▸ huD)
      · exact hnotadj u huD hadj
  · rintro ⟨v, hsub⟩ hdom
    exact dominating_compl_excludes_closed_nbr G D hdom v hsub

theorem two_compl_bad_is_leaf_nbr
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 3 ≤ Fintype.card α)
    (U : Finset α) (hUcard : U.card = 2)
    (hbad : ¬ IsDominating G.Adj (Finset.univ \ U)) :
    ∃ v ∈ leafVertices G, closedNbr G v = U := by
  classical
  obtain ⟨v, hvSub⟩ := (nondom_iff_has_closed_nbr G (Finset.univ \ U)).mp hbad
  have hsub : closedNbr G v ⊆ U := by
    simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ U)] using hvSub
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨w, hvw⟩ := hconn.preconnected.exists_adj_of_nontrivial v
  have hne : v ≠ w := by
    intro heq
    subst w
    exact G.irrefl hvw
  have hvN : v ∈ closedNbr G v := by simp [closedNbr]
  have hwN : w ∈ closedNbr G v := by simp [closedNbr, hvw]
  have hpairSub : ({v,w} : Finset α) ⊆ closedNbr G v := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hvN
    · simpa [Finset.mem_singleton.mp hu] using hwN
  have hpair : ({v,w} : Finset α).card = 2 := by simp [hne]
  have hNcard : (closedNbr G v).card = 2 := by
    have h1 := Finset.card_le_card hpairSub
    have h2 := Finset.card_le_card hsub
    omega
  have hEq : closedNbr G v = U :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have huniq : ∀ y : α, G.Adj v y → y = w := by
    intro y hy
    have hyN : y ∈ closedNbr G v := by simp [closedNbr, hy]
    have hyPair : y ∈ ({v,w} : Finset α) := by
      have hclosedPair : closedNbr G v = ({v,w} : Finset α) :=
        Finset.eq_of_subset_of_card_le hpairSub (by omega) |>.symm
      rw [← hclosedPair]
      exact hyN
    rcases Finset.mem_insert.mp hyPair with h | h
    · subst y; exact False.elim (G.irrefl hy)
    · exact Finset.mem_singleton.mp h
  have hdeg : G.degree v = 1 :=
    (G.degree_eq_one_iff_existsUnique_adj).mpr ⟨w, hvw, huniq⟩
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hdeg⟩, hEq⟩

theorem forbidden_pairs_eq_leaf_nbr_image
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 3 ≤ Fintype.card α) :
    forbiddenPairs G = (leafVertices G).image (closedNbr G) := by
  classical
  ext U
  constructor
  · intro hU
    have hprops := Finset.mem_filter.mp hU
    obtain ⟨v, hvleaf, heq⟩ :=
      two_compl_bad_is_leaf_nbr G hconn hn U
        (Finset.mem_powersetCard.mp hprops.1).2 hprops.2
    exact Finset.mem_image.mpr ⟨v, hvleaf, heq⟩
  · intro hU
    obtain ⟨v, hvleaf, heq⟩ := Finset.mem_image.mp hU
    have hcard := leaf_closed_nbr_card_two G v (Finset.mem_filter.mp hvleaf).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.subset_univ _, heq ▸ hcard⟩
    · rw [← heq]
      intro hdom
      have hbad := dominating_compl_excludes_closed_nbr G
        (Finset.univ \ closedNbr G v) hdom v
      apply hbad
      simp

/-- In any connected graph n>=3, exactly the leaf closed neighborhoods are
the two-element complements of nondominating sets. -/
theorem forbidden_pairs_count_eq_leaves
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 3 ≤ Fintype.card α) :
    (forbiddenPairs G).card = (leafVertices G).card := by
  classical
  rw [forbidden_pairs_eq_leaf_nbr_image G hconn hn]
  apply Finset.card_image_of_injOn
  intro v hv w hw hEq
  by_contra hne
  exact distinct_degree_one_closed_nbr G hconn hn v w
    (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2 hne hEq

/-- Manuscript d_(n-2) identity in subtraction-free integer form. -/
theorem penultimate_domination_coefficient_exact
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    [DecidablePred (IsDominating G.Adj)]
    (hconn : G.Connected) (hn : 5 ≤ Fintype.card α) :
    (domRank G.Adj (Fintype.card α - 2)).card +
      (leafVertices G).card = (Fintype.card α).choose 2 := by
  classical
  let n := Fintype.card α
  let B : Finset (Finset α) := forbiddenPairs G
  let Good : Finset (Finset α) :=
    (Finset.univ.powersetCard 2).filter
      (fun U => IsDominating G.Adj (Finset.univ \ U))
  have hGood : Good =
      (Finset.univ.powersetCard 2 : Finset (Finset α)) \ B := by
    ext U
    simp only [Good, B, forbiddenPairs, Finset.mem_sdiff,
      Finset.mem_filter]
    constructor
    · rintro ⟨hp, hd⟩
      exact ⟨hp, fun hc => hc.2 hd⟩
    · rintro ⟨hp, hc⟩
      refine ⟨hp, ?_⟩
      by_contra hnot
      exact hc ⟨hp, hnot⟩
  have hGoodImage : Good = (domRank G.Adj (n-2)).image
      (fun D : Finset α => Finset.univ \ D) := by
    ext U
    constructor
    · intro hU
      have hprops := Finset.mem_filter.mp hU
      have hcard : (Finset.univ \ U).card = n-2 := by
        have hpart := Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ U)
        simp only [Finset.card_univ] at hpart
        have hU2 := (Finset.mem_powersetCard.mp hprops.1).2
        omega
      apply Finset.mem_image.mpr
      refine ⟨Finset.univ \ U, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨hcard, hprops.2⟩⟩
      · simpa using (Finset.sdiff_sdiff_eq_self (Finset.subset_univ U)).symm
    · intro hU
      obtain ⟨D, hD, heq⟩ := Finset.mem_image.mp hU
      have hprops : D.card = n - 2 ∧ IsDominating G.Adj D :=
        (Finset.mem_filter.mp hD).2
      have hDcard : (Finset.univ \ D).card = 2 := by
        have hpart := Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ D)
        simp only [Finset.card_univ] at hpart
        omega
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, heq ▸ hDcard⟩
      · simpa [← heq] using hprops.2
  have hImageCard : Good.card = (domRank G.Adj (n-2)).card := by
    rw [hGoodImage]
    apply Finset.card_image_of_injOn
    intro D hD E hE heq
    have h := congrArg (fun U : Finset α => Finset.univ \ U) heq
    simpa using h
  have hBsub : B ⊆ (Finset.univ.powersetCard 2 : Finset (Finset α)) := by
    intro U hU
    simp only [B, forbiddenPairs, Finset.mem_filter] at hU
    exact hU.1
  have hpartition := Finset.card_sdiff_add_card_eq_card hBsub
  rw [← hGood] at hpartition
  rw [hImageCard] at hpartition
  have hBcard := forbidden_pairs_count_eq_leaves G hconn (by omega)
  change B.card = (leafVertices G).card at hBcard
  rw [hBcard] at hpartition
  simp only [Finset.card_powersetCard, Finset.card_univ] at hpartition
  exact hpartition

end FinalVerificationP24TopTwo
