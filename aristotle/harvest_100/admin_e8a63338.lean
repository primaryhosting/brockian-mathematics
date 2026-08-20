/-
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- NOTE: the header above is the requested header comment, written as a plain block
-- comment (`/- ... -/`) rather than a module docstring (`/-! ... -/`), because Lean 4
-- rejects any `import` command that follows a module docstring, and `import Mathlib`
-- is required for this proof.

import Mathlib

/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Cassini's identity at `n = 10`: `F 9 * F 11 - F 10 ^ 2 = (-1) ^ 10`.

Derived from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq :
  ∀ (n : ℤ), Int.fib (n + 1) * Int.fib (n - 1) - Int.fib n ^ 2 = (-1) ^ n.natAbs`. -/
theorem cassini_10 :
    (Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1) ^ 10 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 10
  norm_num at h
  have h9 : Int.fib 9 = (Nat.fib 9 : ℤ) := by
    rw [show (9 : ℤ) = ((9 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have h10 : Int.fib 10 = (Nat.fib 10 : ℤ) := by
    rw [show (10 : ℤ) = ((10 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have h11 : Int.fib 11 = (Nat.fib 11 : ℤ) := by
    rw [show (11 : ℤ) = ((11 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  rw [h9, h10, h11] at h
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

