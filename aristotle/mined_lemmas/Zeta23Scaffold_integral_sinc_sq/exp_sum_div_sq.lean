/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Dirichlet-type integral `∫_ℝ (sin x / x)^2 dx = π`.

The proof goes through the Fourier inversion formula applied to the triangle function
`tri ξ = max (1 - |ξ|) 0`, whose Fourier transform is `x ↦ sinc (π x)^2`.
-/

open MeasureTheory Real intervalIntegral
open scoped FourierTransform RealInnerProductSpace

namespace Zeta23Scaffold

/-- The triangle function `ξ ↦ max (1 - |ξ|) 0`, viewed as a complex-valued function. -/

lemma exp_sum_div_sq (x : ℝ) (hx : x ≠ 0) :
    (Complex.exp (((-2 * π * x : ℝ) : ℂ) * Complex.I)
      + Complex.exp (-(((-2 * π * x : ℝ) : ℂ) * Complex.I)) - 2)
      / (((-2 * π * x : ℝ) : ℂ) * Complex.I) ^ 2 = ((Real.sinc (π * x) ^ 2 : ℝ) : ℂ) := by
  set θ : ℝ := -2 * π * x with hθ
  have e1 : Complex.exp ((θ : ℂ) * Complex.I)
      = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have e2 : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have e3 : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)
      = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [e1, e2, e3]
  have hsq : ((θ : ℂ) * Complex.I) ^ 2 = ((-(θ ^ 2) : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hsq]
  have hnum : (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I
      + ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I) - 2
      = ((2 * Real.cos θ - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hnum, ← Complex.ofReal_div]
  norm_cast
  have hπx : π * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  rw [Real.sinc_of_ne_zero hπx]
  have hcos : Real.cos θ = 1 - 2 * Real.sin (π * x) ^ 2 := by
    have h : θ = -(2 * (π * x)) := by rw [hθ]; ring
    rw [h, Real.cos_neg, Real.cos_two_mul, ← Real.sin_sq_add_cos_sq (π * x)]
    ring
  rw [hcos]
  have hθ2 : θ ^ 2 = 4 * (π * x) ^ 2 := by rw [hθ]; ring
  rw [hθ2]
  field_simp
  ring

/-- The Fourier transform of the triangle function is `x ↦ sinc (π x) ^ 2`. -/
