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

lemma xi_add (x y : ZMod 12) : xi (x + y) = xi x * xi y := by
  have h : zeta ^ ((x.val + y.val) % 12) = zeta ^ (x.val + y.val) := by
    conv_rhs => rw [← Nat.div_add_mod (x.val + y.val) 12]
    rw [pow_add, pow_mul, zeta_pow_twelve, one_pow, one_mul]
  simp only [xi, ZMod.val_add, h, pow_add]

