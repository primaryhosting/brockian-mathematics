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

lemma integral_sinc_sq_pi_mul : (∫ x : ℝ, Real.sinc (π * x) ^ 2) = 1 := by
  have hinv := tri_continuous.fourierInv_fourier_eq tri_integrable integrable_fourier_tri
  have h0 : 𝓕⁻ (𝓕 tri) 0 = tri 0 := by rw [hinv]
  rw [Real.fourierInv_eq'] at h0
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul] at h0
  have h1 : (∫ v : ℝ, 𝓕 tri v) = ((∫ v : ℝ, Real.sinc (π * v) ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact MeasureTheory.integral_congr_ae (by filter_upwards with v using fourier_tri v)
  rw [h1] at h0
  have htri0 : tri 0 = 1 := by norm_num [tri]
  rw [htri0] at h0
  exact_mod_cast h0

