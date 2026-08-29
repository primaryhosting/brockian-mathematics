import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

open SimpleGraph Finset

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {A : Finset (Fin n) // A.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

lemma kneser_exists_edge (k : ℕ) (hk : 1 ≤ k) :
    ∃ A B : KneserVertex (2 * k) k, (kneserGraph (2 * k) k).Adj A B := by
  classical
  set S : Finset (Fin (2 * k)) := Finset.univ.filter (fun v => (v : ℕ) < k) with hS
  set T : Finset (Fin (2 * k)) := Finset.univ.filter (fun v => ¬ ((v : ℕ) < k)) with hT
  have hcard : S.card + T.card = 2 * k := by
    rw [hS, hT, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hScard : S.card = k := by
    rw [hS]
    have : (Finset.univ.filter (fun v : Fin (2 * k) => (v : ℕ) < k))
        = (Finset.Iio (⟨k, by omega⟩ : Fin (2 * k))) := by
      ext v; simp [Fin.lt_def]
    rw [this, Fin.card_Iio]
  have hTcard : T.card = k := by omega
  have hdisj : Disjoint S T := by
    rw [hS, hT]
    exact Finset.disjoint_filter_filter_not _ _ _
  refine ⟨⟨S, hScard⟩, ⟨T, hTcard⟩, ?_, hdisj⟩
  intro h
  have hSTeq : S = T := congrArg Subtype.val h
  have h0 : (⟨0, by omega⟩ : Fin (2 * k)) ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have := Finset.disjoint_left.mp hdisj h0
  rw [hSTeq] at h0
  exact this h0


/-! ## Base case `n = 2k + 1`: the odd graphs `KG_{2k+1,k}` have chromatic number `3` -/

section OddGraph

open scoped Fin.NatCast

/-- The cyclic interval `{a, a+1, …, a+k-1}` inside `Fin (2k+1)`. -/
