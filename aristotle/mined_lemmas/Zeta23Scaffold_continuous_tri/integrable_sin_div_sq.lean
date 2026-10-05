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

lemma integrable_sin_div_sq : Integrable (fun w : ℝ => (Real.sin (π * w) / (π * w)) ^ 2) := by
  have h0 : Integrable (fun w : ℝ => (1 + (π * w) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' (R := π) Real.pi_ne_zero
  have hbig : Integrable (fun w : ℝ => 2 * (1 + (π * w) ^ 2)⁻¹) := h0.const_mul 2
  refine Integrable.mono' hbig
    ((by measurability : Measurable fun w : ℝ =>
      (Real.sin (π * w) / (π * w)) ^ 2).aestronglyMeasurable) ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact sq_sin_div_le (π * w)

/-! ## Fourier inversion -/

