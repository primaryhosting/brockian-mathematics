import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based sorting algorithm for `3` elements, presented as a (binary)
decision tree.  An internal node `node i j l r` asks the comparison "is the `i`-th
input element smaller than the `j`-th one?" and branches accordingly; a leaf
`leaf p` outputs the permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 3) → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- Running the decision tree on the input whose ranking is the permutation `σ`
(i.e. the `i`-th input element has rank `σ i`): each comparison `i` vs `j`
is answered by the truth value of `σ i < σ j`. -/

theorem sorting_lb_3' (t : DTree) (ht : Sorts t) : 3 ≤ t.depth := by
  have := sorting_lb_3 t ht
  rwa [clog_two_factorial_three] at this

end CS

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

