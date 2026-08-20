/-
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- NOTE: the header above uses `/- -/` rather than `/-! -/` because Lean 4 does not
-- allow a module docstring (`/-! ... -/`) to precede the `import` commands.
import Mathlib

namespace Math

/-- Cassini's identity at `n = 8`: `F(7) * F(9) - F(8) ^ 2 = (-1) ^ 8`,
where `F = Nat.fib`, stated over `ℤ`. -/

theorem cassini_8_of_mathlib :
    (Nat.fib 7 : ℤ) * (Nat.fib 9 : ℤ) - (Nat.fib 8 : ℤ) ^ 2 = (-1) ^ 8 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 8
  have e7 : Int.fib (7 : ℤ) = (Nat.fib 7 : ℤ) := by
    rw [show ((7 : ℤ)) = ((7 : ℕ) : ℤ) from rfl, Int.fib_natCast]
  have e8 : Int.fib (8 : ℤ) = (Nat.fib 8 : ℤ) := by
    rw [show ((8 : ℤ)) = ((8 : ℕ) : ℤ) from rfl, Int.fib_natCast]
  have e9 : Int.fib (9 : ℤ) = (Nat.fib 9 : ℤ) := by
    rw [show ((9 : ℤ)) = ((9 : ℕ) : ℤ) from rfl, Int.fib_natCast]
  rw [show ((8 : ℤ) + 1) = 9 from rfl, show ((8 : ℤ) - 1) = 7 from rfl, e7, e8, e9,
    show ((8 : ℤ)).natAbs = 8 from rfl] at h
  rw [← h]; ring

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

