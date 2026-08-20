import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-
Note: Lean 4 requires `import` to be the first command of a file, so the header
comment above appears immediately after the imports of this file.
-/

namespace CS

/-- A (binary) decision tree over inputs `I` producing outputs `O`.  An internal node
carries an arbitrary boolean query on the input; in a comparison sort the query is a
single comparison `a i < a j`, so this model is *more* general than comparison sorts
and the lower bound proved below applies a fortiori to them. -/
inductive DecisionTree (I O : Type) : Type
  | leaf : O → DecisionTree I O
  | node : (I → Bool) → DecisionTree I O → DecisionTree I O → DecisionTree I O

namespace DecisionTree

variable {I O : Type}

/-- The output produced by running the decision tree on a given input. -/

theorem clog_two_factorial_three : Nat.clog 2 (Nat.factorial 3) = 3 := by decide

/-- The bound is attained: there is a correct depth-`3` decision tree for `3` elements,
so `sorting_lb_3` is not vacuous and is sharp. -/
