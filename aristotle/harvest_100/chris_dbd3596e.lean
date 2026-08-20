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

namespace Ordinal

/-- Casting natural numbers into the ordinals is additive:
`((m + n : ℕ) : Ordinal) = (m : Ordinal) + (n : Ordinal)`.
This is an instance of `Nat.cast_add`, since `Ordinal` is an `AddMonoidWithOne`. -/
theorem natCast_add (m n : ℕ) : ((m + n : ℕ) : Ordinal) = (m : Ordinal) + (n : Ordinal) :=
  Nat.cast_add m n

/-- Casting natural numbers into the ordinals is multiplicative:
`((m * n : ℕ) : Ordinal) = (m : Ordinal) * (n : Ordinal)`.
This restates Mathlib's `Ordinal.natCast_mul` (note `Ordinal` is not a semiring, so the
generic `Nat.cast_mul` does not apply). -/
theorem natCast_mul' (m n : ℕ) : ((m * n : ℕ) : Ordinal) = (m : Ordinal) * (n : Ordinal) :=
  Ordinal.natCast_mul m n

end Ordinal

#print axioms Ordinal.natCast_add
#print axioms Ordinal.natCast_mul'

