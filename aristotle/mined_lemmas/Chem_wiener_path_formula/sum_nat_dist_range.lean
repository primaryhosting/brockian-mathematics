/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices, i.e. half the sum of `dist u v` over all ordered pairs. -/

theorem sum_nat_dist_range (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Nat.dist i j = 2 * Nat.choose (n + 1) 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ∀ i ∈ Finset.range n,
          ∑ j ∈ Finset.range (n + 1), Nat.dist i j
            = (∑ j ∈ Finset.range n, Nat.dist i j) + (n - i) := by
        intro i hi
        rw [Finset.sum_range_succ, Nat.dist_eq_sub_of_le (by simp at hi; omega)]
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih, sum_range_sub_eq_choose]
      have h2 : ∑ j ∈ Finset.range (n + 1), Nat.dist n j
          = Nat.choose (n + 1) 2 := by
        rw [Finset.sum_range_succ, Nat.dist_self, Nat.add_zero, ← sum_range_sub_eq_choose n]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Nat.dist_eq_sub_of_le_right (by simp at hi; omega)]
      rw [h2]
      have h3 : Nat.choose (n + 1 + 1) 3 = Nat.choose (n + 1) 2 + Nat.choose (n + 1) 3 := by
        rw [Nat.choose_succ_succ (n + 1) 2]
      omega

/-- **Wiener index of the path graph.** The Wiener index of `P n` is `C(n+1, 3)`. -/
