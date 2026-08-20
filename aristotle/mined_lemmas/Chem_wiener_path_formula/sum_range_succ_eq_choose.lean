import Mathlib

open scoped BigOperators
open scoped Nat

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices.  It is computed here as half of the sum over all
ordered pairs (the diagonal contributes `0`). -/

lemma sum_range_succ_eq_choose (n : ℕ) : ∑ i ∈ range n, (i + 1) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ (n + 1) 1]
      simp [Nat.add_comm]

