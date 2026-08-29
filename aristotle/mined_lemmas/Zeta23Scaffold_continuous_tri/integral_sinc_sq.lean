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
open scoped Classical
open scoped FourierTransform

open MeasureTheory Complex

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-! ## The tent function and its Fourier transform

The proof of `∫ (sin x / x) ^ 2 dx = π` goes through Fourier inversion applied to the
tent (triangle) function `x ↦ max 0 (1 - |x|)`, whose Fourier transform is
`w ↦ (sin (π w) / (π w)) ^ 2`. -/

/-- The triangle (tent) function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function. -/

theorem integral_sinc_sq : (∫ x : ℝ, (Real.sin x / x) ^ 2) = π := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => (Real.sin x / x) ^ 2) π
  rw [integral_sin_div_pi_sq] at h
  rw [smul_eq_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ π⁻¹)] at h
  have h2 : π * 1 = π * (π⁻¹ * ∫ y : ℝ, (Real.sin y / y) ^ 2) := by rw [← h]
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul] at h2
  exact h2.symm

end Zeta23Scaffold

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

