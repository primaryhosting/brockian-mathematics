import Mathlib

/-!
# Cassini 13
Category: Pure Mathematics
Target: Math.cassini_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cassini's identity at `n = 13`**: `F(12) · F(14) − F(13)² = (−1)^13`.

Derived from Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq`, which states
`fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ n.natAbs` for `n : ℤ`. -/
theorem cassini_13 :
    (Nat.fib 12 : ℤ) * (Nat.fib 14 : ℤ) - (Nat.fib 13 : ℤ) ^ 2 = (-1) ^ 13 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 13
  rw [show ((13 : ℤ) + 1) = ((14 : ℕ) : ℤ) by norm_num,
      show ((13 : ℤ) - 1) = ((12 : ℕ) : ℤ) by norm_num,
      show (13 : ℤ) = ((13 : ℕ) : ℤ) by norm_num] at h
  simp only [Int.fib_natCast] at h
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

