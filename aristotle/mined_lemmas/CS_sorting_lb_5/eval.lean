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

def eval (p : Equiv.Perm (Fin 5)) : DTree α → α
  | leaf a => a
  | node i j l r => if p i < p j then eval p l else eval p r

/-- The list of leaf labels of the tree, left to right. -/
