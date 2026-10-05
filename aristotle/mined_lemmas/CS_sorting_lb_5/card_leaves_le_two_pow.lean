/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree for sorting `5` elements.
A `node (a, b) l r` compares the input entries at positions `a` and `b`, continuing in `l`
if the comparison oracle answers `true` and in `r` otherwise; a `leaf p` outputs the
permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 × Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- Worst-case number of comparisons performed by the tree. -/

theorem card_leaves_le_two_pow (t : DTree) : (leaves t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node c l r ihl ihr =>
      have h : (leaves (node c l r)).card ≤ (leaves l).card + (leaves r).card := by
        simpa [leaves] using Finset.card_union_le (leaves l) (leaves r)
      refine h.trans ?_
      have hl : (leaves l).card ≤ 2 ^ max (depth l) (depth r) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : (leaves r).card ≤ 2 ^ max (depth l) (depth r) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (leaves l).card + (leaves r).card
          ≤ 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) := Nat.add_le_add hl hr
        _ = 2 ^ depth (node c l r) := by
              have hd : depth (node c l r) = max (depth l) (depth r) + 1 := by
                simp [depth, Nat.add_comm]
              rw [hd, pow_succ]
              ring

/-- Every output of the tree is one of its leaf labels. -/
