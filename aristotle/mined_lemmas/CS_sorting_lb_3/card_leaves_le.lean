/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/`: a module docstring is a
-- command and Lean 4 does not permit it before the `import` line.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-! ## The comparison-sort decision-tree model on 3 elements

An input to a comparison sort on 3 distinct keys is described, up to order
isomorphism, by the permutation `σ : Equiv.Perm (Fin 3)` giving the *rank*
`σ i` of the key stored at position `i`.

A deterministic comparison sort is a binary decision tree: each internal node
compares the keys at two positions `i` and `j` (the only information the
algorithm may extract from the input), and branches on the outcome; each leaf
outputs a permutation, the claimed ranking of the input. -/

/-- A comparison-based decision tree for sorting 3 elements. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 3) → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- Running the decision tree on the input whose ranking is `σ`: the comparison
at a node `node i j l r` asks whether the key at position `i` is smaller than
the key at position `j`, i.e. whether `σ i < σ j`. -/

theorem card_leaves_le (t : DTree) : t.leaves.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j l r ihl ihr =>
      refine (Finset.card_union_le _ _).trans ?_
      have hl : l.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc l.leaves.card + r.leaves.card
          ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := by omega
        _ = 2 ^ (max l.depth r.depth + 1) := by ring
        _ = 2 ^ (node i j l r).depth := rfl

/-- A correct sorting tree must have at least `3! = 6` leaves: it realizes every
one of the `3!` possible rankings as an output. -/
