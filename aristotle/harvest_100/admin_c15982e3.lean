/-
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Cassini's identity at `n = 8`: `F(7) * F(9) - F(8)^2 = (-1)^8`,
where `F` is the Fibonacci sequence `Nat.fib` (so `F 7 = 13`, `F 8 = 21`, `F 9 = 34`). -/
theorem cassini_8 :
    (Nat.fib 7 : ℤ) * (Nat.fib 9 : ℤ) - (Nat.fib 8 : ℤ) ^ 2 = (-1) ^ 8 := by
  norm_num

/-- The same instance of Cassini's identity, obtained from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq :
  ∀ (n : ℤ), Int.fib (n + 1) * Int.fib (n - 1) - Int.fib n ^ 2 = (-1) ^ n.natAbs`. -/
theorem cassini_8_int :
    Int.fib 9 * Int.fib 7 - Int.fib 8 ^ 2 = (-1) ^ 8 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 8
  norm_num at h ⊢
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

