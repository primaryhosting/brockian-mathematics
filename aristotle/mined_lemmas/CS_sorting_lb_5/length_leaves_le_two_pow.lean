/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree over `5` elements returning results of type `α`.
A `node i j l r` compares the input entries at positions `i` and `j`, continuing in `l`
if the `i`-th entry is smaller and in `r` otherwise. -/
inductive DTree (α : Type*) where
  | leaf : α → DTree α
  | node : Fin 5 → Fin 5 → DTree α → DTree α → DTree α

namespace DTree

variable {α : Type*}

/-- The worst-case number of comparisons performed by the tree. -/

lemma length_leaves_le_two_pow (t : DTree α) : t.leaves.length ≤ 2 ^ t.depth := by
  induction t with
  | leaf a => simp [leaves, depth]
  | node i j l r ihl ihr =>
      have hl : l.leaves.length ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.length ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      simp only [leaves, depth, List.length_append, pow_succ]
      omega

end DTree

/-- **Comparison-sort lower bound for 5 elements.**
Any comparison-based decision tree that correctly determines the ordering of `5` elements
(i.e. on every input ordering `p` it outputs `p`) must have worst-case depth at least
`⌈log₂ (5!)⌉ = 7`. -/
