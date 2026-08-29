import Mathlib
/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cassini's identity** at `n = 11`:
`F(10) * F(12) - F(11) ^ 2 = (-1) ^ 11`, stated over `ℤ`.

This is the `n = 11` instance of Mathlib's Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`; the proof below simply evaluates the
Fibonacci numbers `Nat.fib 10 = 55`, `Nat.fib 11 = 89`, `Nat.fib 12 = 144`. -/
theorem cassini_11 :
    (Nat.fib 10 : ℤ) * (Nat.fib 12 : ℤ) - (Nat.fib 11 : ℤ) ^ 2 = (-1 : ℤ) ^ 11 := by
  norm_num

/-- The same statement obtained directly from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`, specialised at `n = 11`. -/
theorem cassini_11_of_mathlib :
    (Int.fib 12 : ℤ) * (Int.fib 10 : ℤ) - (Int.fib 11 : ℤ) ^ 2 = (-1 : ℤ) ^ 11 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 11
  norm_num at h ⊢
  exact h

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

