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

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma xi_eq_one_iff (d : ZMod 12) : xi d = 1 ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    have hv : d.val ≠ 0 := fun hv => hd ((ZMod.val_eq_zero d).mp hv)
    exact zeta_pow_ne_one hv (ZMod.val_lt d) h
  · rintro rfl; exact xi_zero

/-- Orthogonality of characters. -/
