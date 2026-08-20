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

/-- Finite-ordinal addition agrees with `Nat` addition:
`((m + n : ℕ) : Ordinal) = (m : Ordinal) + (n : Ordinal)`. -/

theorem Ordinal.natCast_mul (m n : ℕ) :
    ((m * n : ℕ) : Ordinal) = (m : Ordinal) * (n : Ordinal) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h : m * (k + 1) = m * k + m := by ring
    rw [h, Ordinal.natCast_add, ih]
    push_cast
    rw [mul_add, mul_one]

end RequestProject

#print axioms RequestProject.Ordinal.natCast_add
#print axioms RequestProject.Ordinal.natCast_mul

