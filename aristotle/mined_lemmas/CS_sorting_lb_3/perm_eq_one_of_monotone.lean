/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based sorting algorithm for 3 elements, modelled as a decision tree.
An internal node `cmp i j yes no` compares the entries at positions `i` and `j` of the
input, and branches to `yes` if `x i ≤ x j` and to `no` otherwise.  A leaf is labelled
by the permutation the algorithm outputs. -/
inductive CTree where
  | leaf : Equiv.Perm (Fin 3) → CTree
  | cmp : Fin 3 → Fin 3 → CTree → CTree → CTree
  deriving Inhabited

namespace CTree

/-- The result of running the decision tree on the input `x`. -/

lemma perm_eq_one_of_monotone (p : Equiv.Perm (Fin 3)) (h : ∀ a b : Fin 3, a ≤ b → p a ≤ p b) :
    p = 1 := by
  revert h; revert p; decide

/-- Every permutation is a possible output of a correct sorting tree. -/
