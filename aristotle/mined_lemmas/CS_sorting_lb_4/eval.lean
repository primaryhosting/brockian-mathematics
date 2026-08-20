/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree for sorting `4` elements.
A `node (i, j) l r` compares the keys at positions `i` and `j`, descending into `l`
if the key at `i` is smaller and into `r` otherwise.  A `leaf p` outputs the
permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/

def eval : DTree → Equiv.Perm (Fin 4) → Equiv.Perm (Fin 4)
  | leaf p, _ => p
  | node i j l r, σ => if σ i < σ j then eval l σ else eval r σ

/-- A tree *sorts* if, on every input, it outputs the input's key assignment
(equivalently, the permutation needed to sort the input). -/
