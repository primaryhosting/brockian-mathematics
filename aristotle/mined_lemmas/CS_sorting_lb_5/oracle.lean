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

def oracle (p : Equiv.Perm (Fin 5)) : Fin 5 → Fin 5 → Bool := fun a b => decide (p a ≤ p b)

/-- A tree *sorts* if, for every input arrangement, it outputs that arrangement (equivalently,
it correctly identifies the input's order, which is what a comparison sort must do). -/
