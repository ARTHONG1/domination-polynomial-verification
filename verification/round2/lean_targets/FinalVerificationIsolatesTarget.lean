import Mathlib
import domination_gap3.GraphConnectionTheoremCandidate

/-! Fixed target of submitted-paper Lemma 2.3. The reduced graph has vertex
type {v // v ∉ I} and adjacency inherited from G; hI states that I consists
of exactly the isolated vertices. The numerical invariants use explicit
witnesses and bounds, as in the existing submitted Lean formalisation. -/

namespace FinalVerificationIsolates
open GapThreeGraphConnectionAudit

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def reducedRankCard (G : SimpleGraph α) (I : Finset α) (k : ℕ) : ℕ := by
  classical
  exact (domRank (fun (v w : {v : α // v ∉ I}) => G.Adj v.1 w.1) k).card

theorem domination_rank_card_shift
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w)
    (k : ℕ) :
    (domRank G.Adj (k + I.card)).card = reducedRankCard G I k := by
  sorry

theorem domination_rank_below_isolates_zero
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w)
    (k : ℕ) (hk : k < I.card) :
    (domRank G.Adj k).card = 0 := by
  sorry

def IsWeakUnimodal (a : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, (∀ k < m, a k ≤ a (k + 1)) ∧
    (∀ k ≥ m, a (k + 1) ≤ a k)

noncomputable def reducedDR (G : SimpleGraph α) (I : Finset α) (k : ℕ) : ℝ :=
  (reducedRankCard G I k : ℝ)

theorem domination_isolate_unimodal_iff
    (G : SimpleGraph α) [DecidablePred (IsDominating G.Adj)]
    (I : Finset α) (hI : ∀ v, v ∈ I ↔ ∀ w, ¬ G.Adj v w) :
    IsWeakUnimodal (dR G.Adj) ↔ IsWeakUnimodal (reducedDR G I) := by
  sorry

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
  sorry

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
  sorry

end FinalVerificationIsolates
