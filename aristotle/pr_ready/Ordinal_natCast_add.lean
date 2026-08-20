/-!
# Nat Cast Add
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.natCast_add
Statement: Finite-ordinal arithmetic agrees with Nat: for all m n : Nat, ((m + n : Nat) : Ordinal) = (m : Ordinal) + (n : Ordinal), and similarly for multiplication ((m*n : Nat):Ordinal) = (m:Ordinal)*(n:Ordinal).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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


/-!
# Nat Cast Add
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.natCast_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

/-- Casting a sum of naturals into the ordinals agrees with ordinal addition.
Closed by the general `Nat.cast_add` for an `AddMonoidWithOne`. -/
theorem natCast_add (m n : ℕ) : ((m + n : ℕ) : Ordinal) = (m : Ordinal) + (n : Ordinal) :=
  Nat.cast_add m n

/-- Casting a product of naturals into the ordinals agrees with ordinal multiplication.
This is Mathlib's `Ordinal.natCast_mul`; `Nat.cast_mul` does not apply since `Ordinal` is not
a `NonAssocSemiring`. -/
theorem natCast_mul' (m n : ℕ) : ((m * n : ℕ) : Ordinal) = (m : Ordinal) * (n : Ordinal) :=
  Ordinal.natCast_mul m n

end Ordinal

#print axioms Ordinal.natCast_add
#print axioms Ordinal.natCast_mul'

