import Mathlib

/-!
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cassini's identity at `n = 7`**: `F 6 * F 8 - F 7 ^ 2 = (-1) ^ 7`, stated over `ℤ`
for the Fibonacci numbers `Nat.fib`.

The proof specializes Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq : fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ n.natAbs`
to `n = 7`. -/
theorem cassini_7 :
    (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 7
  rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num] at h
  rw [show ((7 : ℕ) : ℤ) + 1 = ((8 : ℕ) : ℤ) by norm_num,
      show ((7 : ℕ) : ℤ) - 1 = ((6 : ℕ) : ℤ) by norm_num,
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

