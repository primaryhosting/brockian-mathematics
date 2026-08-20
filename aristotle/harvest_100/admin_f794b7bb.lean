/-
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cassini's identity at `n = 7`**: `F 6 * F 8 - F 7 ^ 2 = (-1) ^ 7`.

This is the `n = 7` instance of Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq`
(`fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ |n|`), transferred to `Nat.fib`
via `Int.fib_natCast`. -/
theorem cassini_7 : (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 7
  have e6 : Int.fib 6 = (Nat.fib 6 : ℤ) := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e7 : Int.fib 7 = (Nat.fib 7 : ℤ) := by
    rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e8 : Int.fib 8 = (Nat.fib 8 : ℤ) := by
    rw [show (8 : ℤ) = ((8 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  rw [show (7 : ℤ) + 1 = 8 by norm_num, show (7 : ℤ) - 1 = 6 by norm_num, e6, e7, e8,
    show ((7 : ℤ)).natAbs = 7 from rfl] at h
  linarith [h]

/-- The same identity, checked by direct evaluation of the Fibonacci numbers
(`F 6 = 8`, `F 7 = 13`, `F 8 = 21`, and `8 * 21 - 13 ^ 2 = -1`). -/
example : (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
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

