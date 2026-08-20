/-
# Cassini 12
Category: Pure Mathematics
Target: Math.cassini_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cassini 12
Category: Pure Mathematics
Target: Math.cassini_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Cassini's identity at `n = 12`: `F(11) * F(13) - F(12)^2 = (-1)^12`.

The proof specializes Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq`
(Cassini's identity for integer-indexed Fibonacci numbers) to `n = 12`. -/
theorem cassini_12 : (Nat.fib 11 : ℤ) * (Nat.fib 13 : ℤ) - (Nat.fib 12 : ℤ) ^ 2 = (-1) ^ 12 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 12
  rw [show (12 : ℤ) + 1 = ((13 : ℕ) : ℤ) by norm_num,
      show (12 : ℤ) - 1 = ((11 : ℕ) : ℤ) by norm_num,
      show (12 : ℤ) = ((12 : ℕ) : ℤ) by norm_num,
      Int.fib_natCast, Int.fib_natCast, Int.fib_natCast] at h
  rw [mul_comm] at h
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

