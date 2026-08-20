import Mathlib

open scoped BigOperators
open scoped Nat

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices.  It is computed here as half of the sum over all
ordered pairs (the diagonal contributes `0`). -/

lemma sum_natDist_last (n : ℕ) : ∑ i ∈ range n, Nat.dist i n = (n + 1).choose 2 := by
  rw [← sum_range_succ_eq_choose n, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [Nat.dist]
  omega

