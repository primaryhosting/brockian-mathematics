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

lemma fourier_tri (w : ℝ) (hw : w ≠ 0) :
    𝓕 tri w = (((Real.sin (π * w) / (π * w)) ^ 2 : ℝ) : ℂ) := by
  set z : ℂ := ((-2 * π * w : ℝ) : ℂ) * Complex.I with hzdef
  have hz : z ≠ 0 := by
    have hr : (-2 * π * w : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw
    exact mul_ne_zero (by simpa using hr) Complex.I_ne_zero
  have h1 : 𝓕 tri w = ∫ v : ℝ, Complex.exp (z * v) * tri v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, hzdef]
    congr 2
    push_cast
    ring
  rw [h1, integral_exp_mul_tri z hz, quotient_eval w hw z hzdef]

/-! ## Integrability of the squared sinc function -/

