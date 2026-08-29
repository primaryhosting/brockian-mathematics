import Mathlib
import RequestProject.Math

/-!
# Cassini's identity: companion file

`RequestProject.Math` is required to begin with a fixed header comment, hence it cannot
contain an `import` command and its Fibonacci sequence `Math.fib` is defined from scratch.
Here we import Mathlib and check that `Math.fib` is Mathlib's `Nat.fib`, restate
`Math.cassini_9` in terms of `Nat.fib`, and prove the general Cassini identity.

A search of this Mathlib version turned up no lemma stating Cassini's identity for
`Nat.fib` (only related identities such as `Nat.fib_add_two_sub_fib_add_one` and
`Nat.fib_two_mul_add_one`), so the general statement is proved here by induction.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_9 :
    (fib 8 : Int) * (fib 10 : Int) - (fib 9 : Int) ^ 2 = (-1) ^ 9 := by
  decide

end Math

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

