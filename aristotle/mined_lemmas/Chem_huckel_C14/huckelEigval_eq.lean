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

lemma huckelEigval_eq (k : ℕ) (hk : k < 14) :
    ((huckelEigval k : ℝ) : ℂ) = ee (k : ZMod 14) + ee (-(k : ZMod 14)) := by
  have hval : ((k : ZMod 14)).val = k := ZMod.val_natCast_of_lt hk
  rw [ee_add_ee_neg, hval, huckelEigval]

