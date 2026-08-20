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

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma ee_add_neg (k : ZMod 12) : ee k + ee (-k) = lam k := by
  have hmul : ee k * ee (-k) = 1 := by rw [← ee_add, add_neg_cancel, ee_zero]
  have hinv : ee (-k) = (ee k)⁻¹ := by
    field_simp [ee_ne_zero k] at hmul ⊢
    linear_combination hmul
  set x : ℝ := 2 * Real.pi * k.val / 12 with hx
  rw [hinv, ee_eq_exp k, ← Complex.exp_neg, lam]
  rw [show -((x : ℂ) * Complex.I) = (-(x:ℂ)) * Complex.I by ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_cos]
  push_cast [hx]
  ring

/-- The DFT matrix. -/
