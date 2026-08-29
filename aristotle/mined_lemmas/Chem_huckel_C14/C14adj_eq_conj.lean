/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
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

namespace Chem

/-- The standard additive character `ZMod 14 → ℂ`, `j ↦ exp (2πI j / 14)`. -/

lemma C14adj_eq_conj : C14adj = (U14unit : Matrix (ZMod 14) (ZMod 14) ℂ)
    * Matrix.diagonal mu * (↑U14unit⁻¹ : Matrix (ZMod 14) (ZMod 14) ℂ) := by
  have h : (↑U14unit⁻¹ : Matrix (ZMod 14) (ZMod 14) ℂ) = V14 := rfl
  rw [h]
  show C14adj = U14 * Matrix.diagonal mu * V14
  rw [← C14adj_mul_U14, mul_assoc, U14_mul_V14, mul_one]

