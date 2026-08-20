import Mathlib
/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cassini's identity at `n = 4`**: `F 3 * F 5 - F 4 ^ 2 = (-1) ^ 4`.

This is the `n = 4` instance of the general Cassini identity, available in Mathlib as
`Int.fib_succ_mul_fib_pred_sub_fib_sq : ∀ n : ℤ, Int.fib (n + 1) * Int.fib (n - 1) -
Int.fib n ^ 2 = (-1) ^ n.natAbs`. -/
theorem cassini_4 : (Nat.fib 3 : ℤ) * (Nat.fib 5 : ℤ) - (Nat.fib 4 : ℤ) ^ 2 = (-1) ^ 4 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 4
  rw [show ((4 : ℤ) + 1) = ((5 : ℕ) : ℤ) by norm_num,
    show ((4 : ℤ) - 1) = ((3 : ℕ) : ℤ) by norm_num,
    show ((4 : ℤ)) = ((4 : ℕ) : ℤ) by norm_num,
    Int.fib_natCast, Int.fib_natCast, Int.fib_natCast] at h
  rw [show ((4 : ℕ) : ℤ).natAbs = 4 from rfl] at h
  linarith

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

