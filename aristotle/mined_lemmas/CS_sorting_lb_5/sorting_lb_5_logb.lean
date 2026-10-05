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
A `node i j l r` compares the elements at positions `i` and `j`, continuing in `l`
if the `i`-th one is smaller and in `r` otherwise; a `leaf p` outputs the
permutation `p`. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/

theorem sorting_lb_5_logb (t : DTree) (ht : t.Sorts) :
    ⌈Real.logb 2 (Nat.factorial 5)⌉ ≤ (t.depth : ℤ) := by
  rw [ceil_logb_two_factorial_five]
  exact_mod_cast (sorting_lb_5 t ht).2

end CS

#print axioms CS.sorting_lb_5
#print axioms CS.sorting_lb_5_logb

import RequestProject.SortingLb5
import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

