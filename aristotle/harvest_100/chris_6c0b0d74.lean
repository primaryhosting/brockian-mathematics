/-
# Cassini 6
Category: Pure Mathematics
Target: Math.cassini_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- Cassini's identity at `n = 6`: `F(5) * F(7) - F(6)^2 = (-1)^6`,
where `F` is the Fibonacci sequence (`Nat.fib`), computed in `ℤ`. -/
theorem cassini_6 :
    (Nat.fib 5 : ℤ) * (Nat.fib 7 : ℤ) - (Nat.fib 6 : ℤ) ^ 2 = (-1) ^ 6 := by
  norm_num [Nat.fib]

/-- The same statement obtained as an instance of Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`, with `n = 6`. -/
theorem cassini_6' :
    Int.fib 7 * Int.fib 5 - Int.fib 6 ^ 2 = (-1) ^ (6 : ℤ).natAbs :=
  Int.fib_succ_mul_fib_pred_sub_fib_sq 6

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

