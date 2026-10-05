import Mathlib

/-!
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Cassini's identity at `n = 2`: `F 1 * F 3 - F 2 ^ 2 = (-1) ^ 2`. -/

theorem cassini_2_of_mathlib :
    (Nat.fib 1 : ℤ) * Nat.fib 3 - (Nat.fib 2 : ℤ) ^ 2 = (-1) ^ 2 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 2
  have e3 : Int.fib (2 + 1) = (Nat.fib 3 : ℤ) := by
    rw [show (2 + 1 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e1 : Int.fib (2 - 1) = (Nat.fib 1 : ℤ) := by
    rw [show (2 - 1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e2 : Int.fib 2 = (Nat.fib 2 : ℤ) := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  rw [e3, e1, e2, mul_comm] at h
  simpa using h

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

