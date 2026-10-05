import Mathlib
import RequestProject.Math

/-!
# Cassini 10, via Mathlib's Fibonacci numbers

This file links `Math.fib` (defined in `RequestProject.Math`, which cannot carry an `import`
line) with Mathlib's `Nat.fib`, and derives the `n = 10` case of Cassini's identity from
Mathlib's general statement `Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_10 :
    (fib 9 : Int) * (fib 11 : Int) - (fib 10 : Int) ^ 2 = (-1) ^ 10 := by
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

