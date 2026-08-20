/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

set_option grind.warning false

namespace Chem

open Complex Matrix

/-- The primitive 14-th root of unity `exp(2πi/14)`. -/

lemma eigval_eq (k : Fin 14) :
    eigval k = om ^ ((k.val : ℤ)) + om ^ (-(k.val : ℤ)) := by
  have h1 : ((2 * Real.pi * k.val / 14 : ℝ) : ℂ) * Complex.I
      = ((k.val : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 14) := by push_cast; ring
  have h2 : -((2 * Real.pi * k.val / 14 : ℝ) : ℂ) * Complex.I
      = ((-(k.val : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 14) := by push_cast; ring
  have h3 : eigval k = 2 * Complex.cos ((2 * Real.pi * k.val / 14 : ℝ) : ℂ) := by
    rw [eigval, Complex.ofReal_mul, Complex.ofReal_cos]
    norm_num
  rw [h3, Complex.two_cos, h1, h2, Complex.exp_int_mul, Complex.exp_int_mul, om]

