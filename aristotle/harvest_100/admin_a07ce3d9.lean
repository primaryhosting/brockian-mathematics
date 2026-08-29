/-
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cassini's identity at `n = 11`**: `F(10) * F(12) - F(11) ^ 2 = (-1) ^ 11`.

The proof specializes Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq : ∀ (n : ℤ), Int.fib (n + 1) * Int.fib (n - 1)
  - Int.fib n ^ 2 = (-1) ^ n.natAbs`
to `n = 11`, transferring between `Int.fib` and `Nat.fib` via `Int.fib_natCast`. -/
theorem cassini_11 :
    (Nat.fib 10 : ℤ) * (Nat.fib 12 : ℤ) - (Nat.fib 11 : ℤ) ^ 2 = (-1) ^ 11 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 11
  have h12 : Int.fib (11 + 1) = (Nat.fib 12 : ℤ) := by
    rw [show ((11 : ℤ) + 1) = ((12 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have h10 : Int.fib (11 - 1) = (Nat.fib 10 : ℤ) := by
    rw [show ((11 : ℤ) - 1) = ((10 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have h11 : Int.fib 11 = (Nat.fib 11 : ℤ) := by
    rw [show ((11 : ℤ)) = ((11 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  rw [h12, h10, h11, show ((11 : ℤ).natAbs) = 11 from rfl] at h
  linarith [h]

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

