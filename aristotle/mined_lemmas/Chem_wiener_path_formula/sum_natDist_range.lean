import Mathlib

open scoped BigOperators
open scoped Nat

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices.  It is computed here as half of the sum over all
ordered pairs (the diagonal contributes `0`). -/

lemma sum_natDist_range (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, Nat.dist i j = 2 * (n + 1).choose 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ∀ i ∈ range n, ∑ j ∈ range (n + 1), Nat.dist i j
          = (∑ j ∈ range n, Nat.dist i j) + Nat.dist i n := fun i _ => Finset.sum_range_succ _ _
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih, sum_natDist_last,
        Finset.sum_range_succ]
      have h2 : ∑ j ∈ range n, Nat.dist n j = (n + 1).choose 2 := by
        rw [← sum_natDist_last n]
        exact Finset.sum_congr rfl fun i _ => Nat.dist_comm n i
      rw [h2, Nat.dist_self]
      have h3 : (n + 2).choose 3 = (n + 1).choose 2 + (n + 1).choose 3 :=
        Nat.choose_succ_succ (n + 1) 2
      have h4 : (n + 1 + 1).choose 3 = (n + 2).choose 3 := rfl
      omega

/-- **The Wiener index of the path graph `P_n` is `C(n+1, 3)`.** -/
