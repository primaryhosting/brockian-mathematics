import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
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

namespace Zeta23Scaffold

open MeasureTheory Real Complex
open scoped FourierTransform

/-! ### The triangular (tent) function and its Fourier transform -/

/-- The tent function `t ↦ max (1 - |t|) 0`, real valued. -/

lemma sum_ee (c : ℝ) : ee c (-1) + ee c 1 = 2 * Complex.cos (c : ℂ) := by
  have h1 : ee c (-1) = Complex.exp ((c : ℂ) * I) := by rw [ee]; norm_num
  have h2 : ee c 1 = Complex.exp ((-c : ℂ) * I) := by rw [ee]; norm_num
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The (complexified) tent integral, for a nonzero frequency. -/
