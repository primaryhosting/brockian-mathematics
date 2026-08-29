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

lemma ee_add_ee_neg (k : ZMod 14) :
    ee k + ee (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ) := by
  have hx : ee k = Complex.exp (((2 * Real.pi * k.val / 14 : ℝ) : ℂ) * Complex.I) := by
    rw [ee_apply]; push_cast; ring_nf
  rw [AddChar.map_neg_eq_inv, hx, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos, neg_mul]

/-! ### The eigenvalue equation -/

/-- The key computation: applying the adjacency matrix to the character vector. -/
