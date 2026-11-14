import Mathlib
import domination_gap3.GraphConnectionTheoremCandidate
import domination_gap3.GraphLevelIncidenceTheoremCandidate
import domination_gap3.FinalVerificationP24IntegerBoundCandidate

/-! Candidate corresponding to FinalVerificationP24FinalTarget.
  Target has only Mathlib and GraphConnectionTheoremCandidate imports.
-/

namespace FinalVerificationP24Final
open GapThreeGraphConnectionAudit

def IsStar {α : Type*} (G : SimpleGraph α) : Prop :=
  ∃ c : α, ∀ v : α, v ≠ c →
    G.Adj c v ∧ ∀ w : α, G.Adj v w → w = c

variable {α : Type*} [Fintype α] [DecidableEq α]
  (G : SimpleGraph α) [DecidableRel G.Adj]
  [DecidablePred (IsDominating G.Adj)]

private theorem large_dom (hconn : G.Connected)
    (hn : 2 ≤ Fintype.card α) (S : Finset α)
    (hS : S.card = Fintype.card α - 1) : IsDominating G.Adj S := by
  classical
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  intro v
  by_cases hv : v ∈ S
  · exact Or.inl hv
  · obtain ⟨w, hvw⟩ := hconn.preconnected.exists_adj_of_nontrivial v
    have hw : w ∈ S := by
      by_contra hw
      have hcompl : (Finset.univ \ S).card = 1 := by
        have hpart := Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ S)
        simp only [Finset.card_univ] at hpart
        omega
      have hvcompl : v ∈ (Finset.univ \ S) := by simp [hv]
      have hwcompl : w ∈ (Finset.univ \ S) := by simp [hw]
      have hne : v ≠ w := G.ne_of_adj hvw
      have hsub : ({v, w} : Finset α) ⊆ (Finset.univ \ S) := by
        intro u hu
        rcases Finset.mem_insert.mp hu with h | h
        · exact h ▸ hvcompl
        · exact (Finset.mem_singleton.mp h) ▸ hwcompl
      have hcard := Finset.card_le_card hsub
      have hp : ({v, w} : Finset α).card = 2 := by simp [hne]
      omega
    exact Or.inr ⟨w, hw, hvw⟩

private theorem count_all (hconn : G.Connected) (hn : 2 ≤ Fintype.card α) :
    (domRank G.Adj (Fintype.card α)).card = 1 := by
  classical
  have hEq : domRank G.Adj (Fintype.card α) =
      {Finset.univ} := by
    ext S
    simp only [domRank, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hsc, _⟩
      exact Finset.eq_of_subset_of_card_le (Finset.subset_univ S)
        (by simpa using (le_of_eq hsc.symm))
    · intro hs
      subst S
      constructor
      · simp
      · intro v
        exact Or.inl (Finset.mem_univ v)
  rw [hEq]
  simp

theorem top_minus_one_count (hconn : G.Connected)
    (hn : 2 ≤ Fintype.card α) :
    (domRank G.Adj (Fintype.card α - 1)).card = Fintype.card α := by
  classical
  have hEq : domRank G.Adj (Fintype.card α - 1) =
      Finset.univ.powersetCard (Fintype.card α - 1) := by
    ext S
    constructor
    · intro hs
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, (Finset.mem_filter.mp hs).2.1⟩
    · intro hs
      have hsc := (Finset.mem_powersetCard.mp hs).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨hsc, large_dom G hconn hn S hsc⟩⟩
  rw [hEq, Finset.card_powersetCard, Finset.card_univ]
  have hcard : Fintype.card α - (Fintype.card α - 1) = 1 := by omega
  rw [Nat.choose_symm (k := 1) (by omega : 1 ≤ Fintype.card α),
    Nat.choose_one_right]

private theorem incidence_real (j : ℕ) (hj : 1 ≤ j) :
    critSum G.Adj j +
      (((Fintype.card α - (j - 1) : ℕ) : ℝ) * dR G.Adj (j - 1)) =
        dR G.Adj j * (j : ℝ) := by
  classical
  have hrank (k : ℕ) :
      GapThreeGraphLevelSynthesisAudit.domRank G.Adj k = domRank G.Adj k := by
    ext S
    simp only [GapThreeGraphLevelSynthesisAudit.domRank, domRank,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hcrit (S : Finset α) :
      GapThreeGraphLevelSynthesisAudit.domCritical G.Adj S = domCritical G.Adj S := by
    ext x
    simp only [GapThreeGraphLevelSynthesisAudit.domCritical, domCritical,
      Finset.mem_filter]
    rfl
  have hinc := GapThreeGraphLevelSynthesisAudit.graph_domination_lemma3_identity
    G.Adj j hj
  have hinc' :
      (∑ U ∈ domRank G.Adj j, (domCritical G.Adj U).card) +
      (Fintype.card α - (j-1)) * (domRank G.Adj (j-1)).card =
        (domRank G.Adj j).card * j := by
    simpa [hrank, hcrit] using hinc
  have hR := congrArg (fun x : ℕ => (x : ℝ)) hinc'
  simpa [critSum, dR, Nat.cast_sum, Nat.cast_mul, Nat.cast_add]
    using hR

theorem last_step (hconn : G.Connected) (hn : 2 ≤ Fintype.card α) :
    critMean G.Adj (Fintype.card α) = 0 ∧
    0 ≤ critMean G.Adj (Fintype.card α - 1) := by
  classical
  let n := Fintype.card α
  have hmn := top_minus_one_count G hconn hn
  have hal := count_all G hconn hn
  have hinc := incidence_real G n (by omega)
  have hstep : n - 1 + 1 = n := by omega
  have hcoef : n - (n-1) = 1 := by omega
  have hz : critSum G.Adj n = 0 := by
    change critSum G.Adj n + ((n - (n-1) : ℕ) : ℝ) * dR G.Adj (n-1) =
      dR G.Adj n * (n : ℝ) at hinc
    change (domRank G.Adj (n-1)).card = n at hmn
    change (domRank G.Adj n).card = 1 at hal
    rw [hcoef] at hinc
    norm_num [dR, hmn, hal] at hinc
    linarith
  constructor
  · change critMean G.Adj n = 0
    simp [critMean, hz]
  · unfold critMean
    apply div_nonneg
    · unfold critSum
      apply Finset.sum_nonneg
      intro U hU
      exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _

private theorem b_positive (hconn : G.Connected)
    (hn : 5 ≤ Fintype.card α) :
    0 < ((domRank G.Adj (Fintype.card α - 2)).card : ℝ) := by
  classical
  let n := Fintype.card α
  let L := (FinalVerificationP24TreeLeaves.leafVertices G).card
  let b := (domRank G.Adj (n - 2)).card
  have hL : L ≤ n - 1 :=
    FinalVerificationP24IntegerBound.connected_leaves_card_le_n_minus_one
      G hconn (by omega)
  have hCoeff : b + L = n.choose 2 :=
    FinalVerificationP24TopTwo.penultimate_domination_coefficient_exact
      G hconn hn
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hLR : (L : ℝ) ≤ (n : ℝ) - 1 := by
    have h := hL
    have hc : (L : ℝ) ≤ ((n-1:ℕ):ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub (by omega : 1 ≤ n)] at hc
    norm_num at hc ⊢
    exact hc
  have hEq : (b : ℝ) + (L : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    calc
      (b : ℝ) + (L : ℝ) = ((b + L : ℕ) : ℝ) := by norm_num
      _ = ((n.choose 2 : ℕ) : ℝ) := by exact_mod_cast hCoeff
      _ = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
        rw [Nat.cast_choose_two ℝ n]
  have hpos : 0 < ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
    apply mul_pos <;> linarith
  change 0 < (b : ℝ)
  nlinarith

private theorem mean_top_formulas (hconn : G.Connected)
    (hn : 5 ≤ Fintype.card α) :
    let n := Fintype.card α
    let b := (domRank G.Adj (n - 2)).card
    let d := (domRank G.Adj (n - 3)).card
    critMean G.Adj (n - 1) = (n : ℝ) - 1 - 2 * (b : ℝ) / (n : ℝ) ∧
    critMean G.Adj (n - 2) = (n : ℝ) - 2 - 3 * (d : ℝ) / (b : ℝ) := by
  classical
  dsimp
  let n := Fintype.card α
  let b := (domRank G.Adj (n - 2)).card
  let d := (domRank G.Adj (n - 3)).card
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hbR : 0 < (b : ℝ) := b_positive G hconn hn
  have hmn : (domRank G.Adj (n - 1)).card = n :=
    top_minus_one_count G hconn (by omega)
  have hi1 := incidence_real G (n-1) (by omega)
  have hi2 := incidence_real G (n-2) (by omega)
  have hs1 : n - 1 - 1 = n - 2 := by omega
  have hs2 : n - 2 - 1 = n - 3 := by omega
  have hc1 : n - (n - 2) = 2 := by omega
  have hc2 : n - (n - 3) = 3 := by omega
  have hNat1 : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hNat2 : ((n-2:ℕ):ℝ) = (n:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  have h1 : critSum G.Adj (n-1) + 2 * (b:ℝ) =
      (n:ℝ) * ((n:ℝ)-1) := by
    dsimp only [dR] at hi1
    rw [hs1,hc1,hmn,hNat1] at hi1
    norm_num at hi1
    exact hi1
  have h2 : critSum G.Adj (n-2) + 3 * (d:ℝ) =
      (b:ℝ) * ((n:ℝ)-2) := by
    dsimp only [dR] at hi2
    rw [hs2,hc2,hNat2] at hi2
    norm_num at hi2
    exact hi2
  constructor
  · rw [critMean, dR, hmn]
    apply (div_eq_iff (ne_of_gt hnR)).mpr
    field_simp [ne_of_gt hnR]
    nlinarith [h1]
  · rw [critMean, dR]
    change critSum G.Adj (n-2) / (b:ℝ) =
      (n:ℝ) - 2 - 3 * (d:ℝ) / (b:ℝ)
    have hsum : critSum G.Adj (n-2) =
        (b:ℝ) * ((n:ℝ)-2) - 3 * (d:ℝ) := by linarith [h2]
    rw [hsum]
    field_simp [ne_of_gt hbR]

/-- Equation (top) in the manuscript, directly for connected graphs. -/
theorem top_jump_le (hconn : G.Connected) (hn : 5 ≤ Fintype.card α) :
    critMean G.Adj (Fintype.card α - 1) -
      critMean G.Adj (Fintype.card α - 2) ≤
        1 - 2 / (Fintype.card α : ℝ) := by
  classical
  let n := Fintype.card α
  let b := (domRank G.Adj (n-2)).card
  let d := (domRank G.Adj (n-3)).card
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hbR : 0 < (b : ℝ) := b_positive G hconn hn
  have hform := mean_top_formulas G hconn hn
  dsimp at hform
  have hcoef := (FinalVerificationP24IntegerBound.connected_top_coefficient_inequality
    G hconn hn).1
  change 3 * (n : ℝ) * (d : ℝ) ≤
      2 * (b : ℝ) * ((b : ℝ) - 1) at hcoef
  have hid : (critMean G.Adj (n-1) - critMean G.Adj (n-2)) -
      (1 - 2 / (n:ℝ)) =
      (3 * (n:ℝ) * (d:ℝ) - 2 * (b:ℝ) * ((b:ℝ)-1)) /
        ((n:ℝ) * (b:ℝ)) := by
    rw [hform.1, hform.2]
    have hnZ : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hnR
    have hbZ : ((domRank G.Adj (Fintype.card α - 2)).card : ℝ) ≠ 0 :=
      ne_of_gt hbR
    field_simp [hnZ, hbZ]
    ring
  have hnum : 3 * (n:ℝ) * (d:ℝ) -
      2 * (b:ℝ) * ((b:ℝ)-1) ≤ 0 := sub_nonpos.mpr hcoef
  have hfrac := div_nonpos_of_nonpos_of_nonneg hnum
    (le_of_lt (mul_pos hnR hbR))
  linarith

private theorem star_iff_max_leaves (hconn : G.Connected)
    (hn : 5 ≤ Fintype.card α) :
    IsStar G ↔ (FinalVerificationP24TreeLeaves.leafVertices G).card =
      Fintype.card α - 1 := by
  classical
  let n := Fintype.card α
  let L := FinalVerificationP24TreeLeaves.leafVertices G
  constructor
  · rintro ⟨c, hc⟩
    have hneigh : G.neighborFinset c = Finset.univ.erase c := by
      ext v
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
      constructor
      · intro hcv
        exact ⟨(G.ne_of_adj hcv).symm, Finset.mem_univ _⟩
      · rintro ⟨hvc, _⟩
        exact (hc v hvc).1
    have hcdeg : G.degree c = n - 1 := by
      rw [SimpleGraph.degree, hneigh]
      simp [n]
    have hnot : G.degree c ≠ 1 := by omega
    have hEq : L = Finset.univ.erase c := by
      ext v
      simp only [L, FinalVerificationP24TreeLeaves.leafVertices,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · intro hv
        have hvc : v ≠ c := by
          intro h
          subst v
          exact hnot hv
        exact ⟨hvc, trivial⟩
      · rintro ⟨hvc, _⟩
        exact (G.degree_eq_one_iff_existsUnique_adj).mpr
          ⟨c, G.symm (hc v hvc).1, (hc v hvc).2⟩
    change L.card = n - 1
    rw [hEq]
    simp [n]
  · intro hL
    have hpart := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ L)
    have hcomp : (Finset.univ \ L).card = 1 := by
      have hp : (Finset.univ \ L).card + L.card = n := by
        simpa only [Finset.card_univ] using hpart
      have hLc : L.card = n - 1 := hL
      omega
    obtain ⟨c, hcen⟩ := Finset.card_eq_one.mp hcomp
    have hother : ∀ v : α, v ≠ c → v ∈ L := by
      intro v hvc
      by_contra hvnot
      have hmem : v ∈ Finset.univ \ L :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvnot⟩
      rw [hcen] at hmem
      exact hvc (Finset.mem_singleton.mp hmem)
    refine ⟨c, ?_⟩
    intro v hvc
    have hvdeg : G.degree v = 1 := by
      exact (Finset.mem_filter.mp (hother v hvc)).2
    obtain ⟨w, hvw, huniq⟩ := (G.degree_eq_one_iff_existsUnique_adj).mp hvdeg
    have hw_notleaf : G.degree w ≠ 1 := by
      intro hwdeg
      have htwo := FinalVerificationP24TreeLeaves.adjacent_degree_one_vertices_force_card_two
        G hconn v w hvw hvdeg hwdeg
      omega
    have hwc : w = c := by
      by_contra hne
      have hwleaf : w ∈ L := hother w hne
      exact hw_notleaf (Finset.mem_filter.mp hwleaf).2
    constructor
    · exact G.symm (hwc ▸ hvw)
    · intro z hvz
      exact (huniq z hvz).trans hwc

private theorem star_rank_lower (hn : 5 ≤ Fintype.card α)
    (hstar : IsStar G) :
    (Fintype.card α - 1).choose 3 ≤
      (domRank G.Adj (Fintype.card α - 3)).card := by
  classical
  let n := Fintype.card α
  obtain ⟨c, hc⟩ := hstar
  let U : Finset α := Finset.univ.erase c
  let Small : Finset (Finset α) := U.powersetCard 3
  let Good : Finset (Finset α) :=
    Small.image (fun V : Finset α => Finset.univ \ V)
  have hsub : Good ⊆ domRank G.Adj (n-3) := by
    intro D hD
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hD
    have hVp := Finset.mem_powersetCard.mp hV
    have hVsub : V ⊆ U := hVp.1
    have hcnot : c ∉ V := by
      intro h
      have hIn : c ∈ U := hVsub h
      exact (Finset.mem_erase.mp hIn).1 rfl
    have hcDom : c ∈ (Finset.univ \ V) :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcnot⟩
    have hDom : IsDominating G.Adj (Finset.univ \ V) := by
      intro v
      by_cases hvc : v = c
      · exact Or.inl (hvc ▸ hcDom)
      · exact Or.inr ⟨c, hcDom, G.symm (hc v hvc).1⟩
    have hSsize : (Finset.univ \ V).card = n-3 := by
      have hpart := Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ V)
      have hs : V.card = 3 := hVp.2
      simp only [Finset.card_univ] at hpart
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨hSsize, hDom⟩⟩
  have hinj : Set.InjOn (fun V : Finset α => Finset.univ \ V) Small := by
    intro V hV W hW heq
    have h := congrArg (fun X : Finset α => Finset.univ \ X) heq
    simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ V),
      Finset.sdiff_sdiff_eq_self (Finset.subset_univ W)] using h
  have hUcard : U.card = n - 1 := by simp [U, n]
  have hGoodCard : Good.card = (n-1).choose 3 := by
    change (Small.image (fun V : Finset α => Finset.univ \ V)).card = _
    rw [Finset.card_image_of_injOn hinj, Finset.card_powersetCard, hUcard]
  have hbound : Good.card ≤ (domRank G.Adj (n-3)).card :=
    Finset.card_le_card hsub
  rw [hGoodCard] at hbound
  exact hbound

private theorem star_coefficient_equality (hconn : G.Connected)
    (hn : 5 ≤ Fintype.card α) (hstar : IsStar G) :
    3 * (Fintype.card α : ℝ) *
      ((domRank G.Adj (Fintype.card α - 3)).card : ℝ) =
    2 * ((domRank G.Adj (Fintype.card α - 2)).card : ℝ) *
      (((domRank G.Adj (Fintype.card α - 2)).card : ℝ) - 1) := by
  classical
  let n := Fintype.card α
  let b := (domRank G.Adj (n-2)).card
  let d := (domRank G.Adj (n-3)).card
  let L := (FinalVerificationP24TreeLeaves.leafVertices G).card
  have hnCast : 5 ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : L = n - 1 := (star_iff_max_leaves G hconn hn).mp hstar
  have hb : b + L = n.choose 2 :=
    FinalVerificationP24TopTwo.penultimate_domination_coefficient_exact G hconn hn
  have hbr : (b:ℝ) = ((n:ℝ)-1) * ((n:ℝ)-2) / 2 := by
    have hBR : (b:ℝ) + (L:ℝ) = (n.choose 2:ℝ) := by exact_mod_cast hb
    have hLReal : (L:ℝ) = (n:ℝ)-1 := by
      rw [hL, Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [Nat.cast_choose_two ℝ n] at hBR
    linarith
  have hc3 : (((n-1).choose 3 : ℕ) : ℝ) =
      ((n:ℝ)-1) * ((n:ℝ)-2) * ((n:ℝ)-3) / 6 := by
    rw [FinalVerificationP24IntegerBound.real_choose_three,
      Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hbase : 3 * (n:ℝ) * (((n-1).choose 3:ℕ):ℝ) =
      2 * (b:ℝ) * ((b:ℝ)-1) := by
    rw [hc3, hbr]
    ring
  have hlower : ((n-1).choose 3:ℝ) ≤ (d:ℝ) := by
    exact_mod_cast star_rank_lower G hn hstar
  have hmul : 3 * (n:ℝ) * (((n-1).choose 3:ℕ):ℝ) ≤
      3 * (n:ℝ) * (d:ℝ) := by
    exact mul_le_mul_of_nonneg_left hlower (by positivity)
  have hupper := (FinalVerificationP24IntegerBound.connected_top_coefficient_inequality
    G hconn hn).1
  change 3*(n:ℝ)*(d:ℝ) ≤ 2*(b:ℝ)*((b:ℝ)-1) at hupper
  linarith

/-- The complete manuscript equality condition, including the sufficient
case of a star, using the original critical-vertex average. -/
theorem top_jump_eq_iff_star (hconn : G.Connected)
    (hn : 5 ≤ Fintype.card α) :
    (critMean G.Adj (Fintype.card α - 1) -
      critMean G.Adj (Fintype.card α - 2) =
        1 - 2 / (Fintype.card α : ℝ)) ↔ IsStar G := by
  classical
  let n := Fintype.card α
  let b := (domRank G.Adj (n-2)).card
  let d := (domRank G.Adj (n-3)).card
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hbR : 0 < (b : ℝ) := b_positive G hconn hn
  have hform := mean_top_formulas G hconn hn
  dsimp at hform
  have hid : (critMean G.Adj (n-1) - critMean G.Adj (n-2)) -
      (1 - 2 / (n:ℝ)) =
      (3 * (n:ℝ) * (d:ℝ) - 2 * (b:ℝ) * ((b:ℝ)-1)) /
        ((n:ℝ) * (b:ℝ)) := by
    rw [hform.1, hform.2]
    have hnZ : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hnR
    have hbZ : ((domRank G.Adj (Fintype.card α - 2)).card : ℝ) ≠ 0 :=
      ne_of_gt hbR
    field_simp [hnZ, hbZ]
    ring
  have hiff :
      (critMean G.Adj (n-1) - critMean G.Adj (n-2) =
        1 - 2 / (n:ℝ)) ↔
      (3*(n:ℝ)*(d:ℝ) = 2*(b:ℝ)*((b:ℝ)-1)) := by
    constructor
    · intro hj
      have hzero : (3*(n:ℝ)*(d:ℝ) - 2*(b:ℝ)*((b:ℝ)-1)) /
          ((n:ℝ)*(b:ℝ)) = 0 := by
        rw [← hid]
        exact sub_eq_zero.mpr hj
      rcases (div_eq_zero_iff).mp hzero with hnum | hden
      · exact sub_eq_zero.mp hnum
      · exact False.elim ((ne_of_gt (mul_pos hnR hbR)) hden)
    · intro heq
      apply sub_eq_zero.mp
      rw [hid, sub_eq_zero.mpr heq]
      simp
  constructor
  · intro hj
    have hcoeff := hiff.mp hj
    have hL := (FinalVerificationP24IntegerBound.connected_top_coefficient_inequality
      G hconn hn).2 hcoeff
    exact (star_iff_max_leaves G hconn hn).mpr hL
  · intro hs
    exact hiff.mpr (star_coefficient_equality G hconn hn hs)

end FinalVerificationP24Final
