import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 15-th root of unity. -/

lemma om_pow_mod (m : ℕ) : om ^ (m % 15) = om ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 15]
  rw [pow_add, pow_mul, om_pow_15, one_pow, one_mul]

/-- The character `j ↦ ω^j` on `Fin 15 ≃ ZMod 15`. -/
