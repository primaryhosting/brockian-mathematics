import Mathlib
/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cassini's identity** at `n = 10`: `F(9) * F(11) - F(10) ^ 2 = (-1) ^ 10`.

This is deduced from Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq`
(Cassini's identity: `fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ |n|`) at `n = 10`. -/
theorem cassini_10 :
    (Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1) ^ 10 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 10
  rw [show (10 : ℤ) + 1 = ((11 : ℕ) : ℤ) by norm_num,
    show (10 : ℤ) - 1 = ((9 : ℕ) : ℤ) by norm_num,
    show (10 : ℤ) = ((10 : ℕ) : ℤ) by norm_num,
    Int.fib_natCast, Int.fib_natCast, Int.fib_natCast, Int.natAbs_natCast] at h
  linear_combination h

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

