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

lemma card_reachable_le (t : CTree) : (reachable t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [reachable, depth]
  | cmp i j yes no ihy ihn =>
      refine (Finset.card_union_le _ _).trans ?_
      have h1 : (2 : ℕ) ^ depth yes ≤ 2 ^ (max (depth yes) (depth no)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2 : ℕ) ^ depth no ≤ 2 ^ (max (depth yes) (depth no)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : (reachable yes).card + (reachable no).card
          ≤ 2 ^ (max (depth yes) (depth no)) + 2 ^ (max (depth yes) (depth no)) := by
        omega
      simp only [depth, pow_succ]
      omega

/-- A monotone permutation of `Fin 3` is the identity. -/
