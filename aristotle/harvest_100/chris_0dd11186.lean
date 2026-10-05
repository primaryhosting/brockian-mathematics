import Mathlib

/-!
# Nat Cast Add
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.natCast_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace RequestProject

/-- Casting natural numbers into the ordinals is additive:
`((m + n : ℕ) : Ordinal) = (m : Ordinal) + (n : Ordinal)`. -/
theorem Ordinal.natCast_add (m n : ℕ) : ((m + n : ℕ) : Ordinal) = (m : Ordinal) + (n : Ordinal) :=
  Nat.cast_add m n

/-- Casting natural numbers into the ordinals is multiplicative:
`((m * n : ℕ) : Ordinal) = (m : Ordinal) * (n : Ordinal)`. -/
theorem Ordinal.natCast_mul (m n : ℕ) : ((m * n : ℕ) : Ordinal) = (m : Ordinal) * (n : Ordinal) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.cast_add, ih, Nat.cast_succ, mul_add, mul_one]

end RequestProject

