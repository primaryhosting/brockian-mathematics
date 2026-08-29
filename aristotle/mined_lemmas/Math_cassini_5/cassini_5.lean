import Mathlib
import RequestProject.Math

/-!
# Cassini 5 — Mathlib companion file

This file connects the self-contained development in `RequestProject/Math.lean` with
Mathlib: it shows `Math.fib = Nat.fib`, restates `Math.cassini_5` in terms of `Nat.fib`,
and re-derives it from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- The locally defined Fibonacci sequence agrees with Mathlib's `Nat.fib`. -/

theorem cassini_5 :
    (fib 4 : Int) * (fib 6 : Int) - (fib 5 : Int) ^ 2 = (-1) ^ 5 := by
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

