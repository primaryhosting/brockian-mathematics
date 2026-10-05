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

/-- Finite-ordinal addition agrees with natural number addition:
the cast of a sum of naturals into `Ordinal` is the sum of the casts.

This is an instance of the general `Nat.cast_add` for `AddMonoidWithOne`,
applied to the `Ordinal.addMonoidWithOne` structure. -/
theorem natCast_add (m n : ℕ) : ((m + n : ℕ) : Ordinal) = (m : Ordinal) + (n : Ordinal) :=
  Nat.cast_add m n

/-- Finite-ordinal multiplication agrees with natural number multiplication.

This restates the existing Mathlib lemma `Ordinal.natCast_mul`. -/
theorem natCast_mul' (m n : ℕ) : ((m * n : ℕ) : Ordinal) = (m : Ordinal) * (n : Ordinal) :=
  Ordinal.natCast_mul m n

end Ordinal

