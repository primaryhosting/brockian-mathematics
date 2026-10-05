/-
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`,
-- so the header above is a plain block comment with identical text.)

import Mathlib

namespace Math

/-- Cassini's identity at `n = 7`: `F 6 * F 8 - F 7 ^ 2 = (-1) ^ 7`,
stated over `ℤ` (since the left-hand side is negative).

This is the `n = 7` instance of the general Cassini identity, available in
Mathlib as `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
theorem cassini_7 :
    (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
  norm_num [Nat.fib]

/-- The same statement derived from the general Cassini identity in Mathlib,
`Int.fib_succ_mul_fib_pred_sub_fib_sq`, specialised to `n = 7`. -/
theorem cassini_7_via_mathlib :
    Int.fib 8 * Int.fib 6 - Int.fib 7 ^ 2 = (-1) ^ 7 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 7
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

