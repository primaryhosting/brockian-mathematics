/-
# Cassini 5
Category: Pure Mathematics
Target: Math.cassini_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 does not permit a module docstring (`/-! ... -/`) before `import`
-- commands, so the required header appears above as an ordinary block comment,
-- and is repeated verbatim as a module docstring immediately after the import.

import Mathlib

/-!
# Cassini 5
Category: Pure Mathematics
Target: Math.cassini_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cassini's identity at `n = 5`**: `F(4) · F(6) − F(5)² = (−1)⁵`.

The proof specializes Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq :`
`∀ (n : ℤ), Int.fib (n + 1) * Int.fib (n - 1) - Int.fib n ^ 2 = (-1) ^ n.natAbs`
to `n = 5`, transporting between `Int.fib` and `Nat.fib` via `Int.fib_natCast`. -/
theorem cassini_5 : (Nat.fib 4 : ℤ) * Nat.fib 6 - (Nat.fib 5 : ℤ) ^ 2 = (-1) ^ 5 := by
  have key := Int.fib_succ_mul_fib_pred_sub_fib_sq 5
  have e6 : Int.fib ((5 : ℤ) + 1) = (Nat.fib 6 : ℤ) := by
    rw [show (5 : ℤ) + 1 = ((6 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e4 : Int.fib ((5 : ℤ) - 1) = (Nat.fib 4 : ℤ) := by
    rw [show (5 : ℤ) - 1 = ((4 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e5 : Int.fib (5 : ℤ) = (Nat.fib 5 : ℤ) := by
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  rw [e6, e4, e5, show Int.natAbs 5 = 5 from rfl] at key
  rw [mul_comm]
  exact key

end Math

#print axioms Math.cassini_5

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

