import Mathlib

/-!
Fixed target for the submitted Section 7 P24 three-subset counting bound.
The final paper also needs a separate tree/leaf bridge (not assumed here).
Proofs in this file are deliberately unfilled reference statements.
-/

namespace FinalVerificationP24Overlap

def tripleSupersets {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset α) : Finset (Finset α) :=
  (Finset.univ.powersetCard 3).filter (fun U => P ⊆ U)

theorem triple_supersets_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset α) (hP : P.card = 2) :
    (tripleSupersets P).card = Fintype.card α - 2 := by
  sorry

theorem distinct_pair_triple_inter_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (P Q : Finset α) (hP : P.card = 2) (hQ : Q.card = 2)
    (hPQ : P ≠ Q) :
    ((tripleSupersets P) ∩ (tripleSupersets Q)).card ≤ 1 := by
  sorry

theorem union_lower_from_pairwise_intersections
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (S : Finset ι) (A : ι → Finset α)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (A i ∩ A j).card ≤ 1) :
    (∑ i ∈ S, (A i).card) ≤ (S.biUnion A).card + S.card.choose 2 := by
  sorry

theorem allowed_triples_bound
    {ι α : Type*} [DecidableEq ι] [Fintype α] [DecidableEq α]
    (S : Finset ι) (P : ι → Finset α)
    (hsize : ∀ i ∈ S, (P i).card = 2)
    (hdistinct : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → P i ≠ P j) :
    (((Finset.univ.powersetCard 3 : Finset (Finset α)) \
      (S.biUnion (fun i => tripleSupersets (P i)))).card +
      S.card * (Fintype.card α - 2) ≤
      (Fintype.card α).choose 3 + S.card.choose 2) := by
  sorry

end FinalVerificationP24Overlap
