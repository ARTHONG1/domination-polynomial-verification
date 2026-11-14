import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace GapThreeGraphLevelSynthesisAudit

/-- Closed-neighborhood domination on a finite vertex type α. -/
def IsDominating {α : Type*} (adj : α → α → Prop) (S : Finset α) : Prop :=
  ∀ v : α, v ∈ S ∨ ∃ u ∈ S, adj v u

/-- The k-rank dominating set family D_k(G) on a finite vertex type α. -/
def domRank {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (k : ℕ) : Finset (Finset α) :=
  Finset.univ.filter (fun S => S.card = k ∧ IsDominating adj S)

/-- Deletion-critical dominating vertices C(S) = a(S). -/
def domCritical {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (S : Finset α) : Finset α :=
  S.filter (fun x => ¬ IsDominating adj (S.erase x))

/-- Removable dominating vertices S \ C(S). -/
def domRemovable {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (S : Finset α) : Finset α :=
  S.filter (fun x => IsDominating adj (S.erase x))

private lemma isDominating_upward {α : Type*} (adj : α → α → Prop)
    {S U : Finset α} (hSU : S ⊆ U) (hS : IsDominating adj S) :
    IsDominating adj U := by
  intro v
  rcases hS v with hvS | ⟨u, huS, hadj⟩
  · exact Or.inl (hSU hvS)
  · exact Or.inr ⟨u, hSU huS, hadj⟩

private lemma domCritical_card_le {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    {S U : Finset α} (hS : IsDominating adj S) (hSU : S ⊆ U) :
    (domCritical adj U).card ≤ (domCritical adj S).card := by
  apply Finset.card_le_card
  intro x hx
  rw [domCritical, Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxU, hxUdel⟩
  refine ⟨?_, ?_⟩
  · by_contra hxS
    apply hxUdel
    apply isDominating_upward adj _ hS
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun hyx => hxS (hyx ▸ hy), hSU hy⟩
  · intro hSdel
    apply hxUdel
    exact isDominating_upward adj (Finset.erase_subset_erase x hSU) hSdel

private def lowerInc {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (j : ℕ) :
    Finset (Σ _ : Finset α, α) :=
  (domRank adj (j - 1)).sigma (fun S => Finset.univ \ S)

private def upperInc {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)] (j : ℕ) :
    Finset (Σ _ : Finset α, α) :=
  (domRank adj j).sigma (fun U => domRemovable adj U)

private lemma sum_domRemovable_eq {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (j : ℕ) (hj : 1 ≤ j) :
    ∑ U ∈ domRank adj j, (domRemovable adj U).card =
      (Fintype.card α - (j - 1)) * (domRank adj (j - 1)).card := by
  have h_low : (lowerInc adj j).card =
      (Fintype.card α - (j - 1)) * (domRank adj (j - 1)).card := by
    rw [lowerInc, Finset.card_sigma]
    have h_congr : ∑ S ∈ domRank adj (j - 1), (Finset.univ \ S).card =
        ∑ _S ∈ domRank adj (j - 1), (Fintype.card α - (j - 1)) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [domRank, Finset.mem_filter] at hS
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hS.2.1]
    rw [h_congr, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
  have h_up : (upperInc adj j).card =
      ∑ U ∈ domRank adj j, (domRemovable adj U).card := by
    rw [upperInc, Finset.card_sigma]
  rw [← h_up, ← h_low]
  symm
  apply Finset.card_bij (fun p _ => ⟨insert p.2 p.1, p.2⟩)
  · rintro ⟨S, x⟩ hp
    rw [lowerInc, Finset.mem_sigma, domRank, Finset.mem_filter, Finset.mem_sdiff] at hp
    rcases hp with ⟨⟨_, hScard, hPS⟩, ⟨_, hxS⟩⟩
    rw [upperInc, Finset.mem_sigma, domRank, Finset.mem_filter,
        domRemovable, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ⟨Finset.mem_insert_self x S, ?_⟩⟩
    · rw [Finset.card_insert_of_notMem hxS, hScard]
      omega
    · exact isDominating_upward adj (Finset.subset_insert x S) hPS
    · rw [Finset.erase_insert hxS]
      exact hPS
  · rintro ⟨S1, x1⟩ hp1 ⟨S2, x2⟩ hp2 heq
    rw [lowerInc, Finset.mem_sigma, Finset.mem_sdiff] at hp1 hp2
    dsimp at hp1 hp2 heq
    injection heq with hU hx
    subst hx
    have h1 := Finset.erase_insert hp1.2.2
    have h2 := Finset.erase_insert hp2.2.2
    have hS : S1 = S2 := by rw [← h1, ← h2, hU]
    subst hS
    rfl
  · rintro ⟨U, x⟩ hq
    rw [upperInc, Finset.mem_sigma, domRank, Finset.mem_filter,
        domRemovable, Finset.mem_filter] at hq
    rcases hq with ⟨⟨_, hUcard, _⟩, ⟨hxU, hPdel⟩⟩
    refine ⟨⟨U.erase x, x⟩, ?_, ?_⟩
    · rw [lowerInc, Finset.mem_sigma, domRank, Finset.mem_filter, Finset.mem_sdiff]
      refine ⟨⟨Finset.mem_univ _, ?_, hPdel⟩, ⟨Finset.mem_univ _, Finset.notMem_erase x U⟩⟩
      rw [Finset.card_erase_of_mem hxU, hUcard]
    · simp [Finset.insert_erase hxU]

/-- 1. Unconditional graph-level proof of Beaton-Schoonhoven Lemma 3. -/
theorem graph_domination_lemma3_identity {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (j : ℕ) (hj : 1 ≤ j) :
    (∑ U ∈ domRank adj j, (domCritical adj U).card) +
      (Fintype.card α - (j - 1)) * (domRank adj (j - 1)).card =
      (domRank adj j).card * j := by
  have h_part : ∑ U ∈ domRank adj j, ((domRemovable adj U).card + (domCritical adj U).card) =
      ∑ _U ∈ domRank adj j, j := by
    apply Finset.sum_congr rfl
    intro U hU
    rw [domRank, Finset.mem_filter] at hU
    have h_add : (domRemovable adj U).card + (domCritical adj U).card = U.card := by
      simpa [domRemovable, domCritical] using
        Finset.card_filter_add_card_filter_not (s := U) (p := fun x => IsDominating adj (U.erase x))
    rw [h_add, hU.2.1]
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, sum_domRemovable_eq adj j hj] at h_part
  omega

/-- 2. Unconditional graph-level weighted incidence critical-sum inequality. -/
theorem graph_domination_weighted_incidence_le {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidablePred (IsDominating adj)]
    (j : ℕ) (hj : 1 ≤ j) :
    ∑ U ∈ domRank adj j, (domRemovable adj U).card * (domCritical adj U).card ≤
      (Fintype.card α - (j - 1)) * ∑ S ∈ domRank adj (j - 1), (domCritical adj S).card := by
  have h_low_sum : ∑ p ∈ lowerInc adj j, (domCritical adj p.1).card =
      (Fintype.card α - (j - 1)) * ∑ S ∈ domRank adj (j - 1), (domCritical adj S).card := by
    rw [lowerInc, Finset.sum_sigma]
    have h_congr : ∑ S ∈ domRank adj (j - 1), ∑ _x ∈ Finset.univ \ S, (domCritical adj S).card =
        ∑ S ∈ domRank adj (j - 1), (Fintype.card α - (j - 1)) * (domCritical adj S).card := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [domRank, Finset.mem_filter] at hS
      dsimp
      rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_sdiff, Finset.inter_univ,
          Finset.card_univ, hS.2.1]
    rw [h_congr, ← Finset.mul_sum]
  have h_up_sum : ∑ p ∈ upperInc adj j, (domCritical adj p.1).card =
      ∑ U ∈ domRank adj j, (domRemovable adj U).card * (domCritical adj U).card := by
    rw [upperInc, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro U _
    dsimp
    rw [Finset.sum_const, Nat.nsmul_eq_mul]
  rw [← h_up_sum, ← h_low_sum]
  have h_bij : ∑ p ∈ upperInc adj j, (domCritical adj p.1).card =
      ∑ p ∈ lowerInc adj j, (domCritical adj (insert p.2 p.1)).card := by
    symm
    apply Finset.sum_bij (fun p _ => ⟨insert p.2 p.1, p.2⟩)
    · rintro ⟨S, x⟩ hp
      rw [lowerInc, Finset.mem_sigma, domRank, Finset.mem_filter, Finset.mem_sdiff] at hp
      rcases hp with ⟨⟨_, hScard, hPS⟩, ⟨_, hxS⟩⟩
      rw [upperInc, Finset.mem_sigma, domRank, Finset.mem_filter,
          domRemovable, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ⟨Finset.mem_insert_self x S, ?_⟩⟩
      · rw [Finset.card_insert_of_notMem hxS, hScard]
        omega
      · exact isDominating_upward adj (Finset.subset_insert x S) hPS
      · rw [Finset.erase_insert hxS]
        exact hPS
    · rintro ⟨S1, x1⟩ hp1 ⟨S2, x2⟩ hp2 heq
      rw [lowerInc, Finset.mem_sigma, Finset.mem_sdiff] at hp1 hp2
      dsimp at hp1 hp2 heq
      injection heq with hU hx
      subst hx
      have h1 := Finset.erase_insert hp1.2.2
      have h2 := Finset.erase_insert hp2.2.2
      have hS : S1 = S2 := by rw [← h1, ← h2, hU]
      subst hS
      rfl
    · rintro ⟨U, x⟩ hq
      rw [upperInc, Finset.mem_sigma, domRank, Finset.mem_filter,
          domRemovable, Finset.mem_filter] at hq
      rcases hq with ⟨⟨_, hUcard, _⟩, ⟨hxU, hPdel⟩⟩
      refine ⟨⟨U.erase x, x⟩, ?_, ?_⟩
      · rw [lowerInc, Finset.mem_sigma, domRank, Finset.mem_filter, Finset.mem_sdiff]
        refine ⟨⟨Finset.mem_univ _, ?_, hPdel⟩, ⟨Finset.mem_univ _, Finset.notMem_erase x U⟩⟩
        rw [Finset.card_erase_of_mem hxU, hUcard]
      · simp [Finset.insert_erase hxU]
    · rintro ⟨S, x⟩ _
      rfl
  rw [h_bij]
  apply Finset.sum_le_sum
  rintro ⟨S, x⟩ hp
  rw [lowerInc, Finset.mem_sigma, domRank, Finset.mem_filter] at hp
  exact domCritical_card_le adj hp.1.2.2 (Finset.subset_insert x S)

/-- 3. Strict central jump c_{i+1} - c_i < 2 excludes weak valley and three-term plateau. -/
theorem strict_jump_excludes_weak_valley_and_three_plateau
    (n i d_prev d_curr d_next c_curr c_next : ℝ)
    (hd_curr : 0 < d_curr) (hd_next : 0 < d_next)
    (hi : i < n)
    (h_id1 : d_curr * (i - c_curr) = (n - i + 1) * d_prev)
    (h_id2 : d_next * (i + 1 - c_next) = (n - i) * d_curr)
    (h_strict_jump : c_next - c_curr < 2) :
    ¬ (d_curr ≤ d_prev ∧ d_curr ≤ d_next) ∧ (d_prev < d_curr ∨ d_next < d_curr) := by
  have h_not_both : ¬ (d_curr ≤ d_prev ∧ d_curr ≤ d_next) := by
    rintro ⟨h1, h2⟩
    have h_ni : 0 ≤ n - i := by linarith
    have h_ni1 : 0 ≤ n - i + 1 := by linarith
    have h_left : (n - i + 1) * d_curr ≤ (n - i + 1) * d_prev := mul_le_mul_of_nonneg_left h1 h_ni1
    have h_right : (n - i) * d_curr ≤ (n - i) * d_next := mul_le_mul_of_nonneg_left h2 h_ni
    have hc1 : c_curr ≤ 2 * i - n - 1 := by
      have : d_curr * (c_curr - (2 * i - n - 1)) ≤ 0 := by linarith
      nlinarith
    have hc2 : 2 * i + 1 - n ≤ c_next := by
      have : 0 ≤ d_next * (c_next - (2 * i + 1 - n)) := by linarith
      nlinarith
    linarith
  refine ⟨h_not_both, ?_⟩
  by_contra h_neg
  push_neg at h_neg
  exact h_not_both h_neg

end GapThreeGraphLevelSynthesisAudit
