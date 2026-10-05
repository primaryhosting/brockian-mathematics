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

lemma integral_sin_div_pi_sq : (∫ w : ℝ, (Real.sin (π * w) / (π * w)) ^ 2) = 1 := by
  have hinv : 𝓕⁻ (𝓕 tri) 0 = tri 0 :=
    integrable_tri.fourierInv_fourier_eq integrable_fourier_tri continuous_tri.continuousAt
  have hleft : 𝓕⁻ (𝓕 tri) 0 = ∫ w : ℝ, 𝓕 tri w := by
    rw [Real.fourierInv_eq]
    simp
  rw [hleft, tri_zero, integral_congr_ae fourier_tri_ae, integral_complex_ofReal] at hinv
  exact_mod_cast hinv

/-- The normalization integral of the sine kernel: `∫ (sin x / x) ^ 2 dx = π`
over the real line, as a Bochner integral with respect to Lebesgue measure.
(The integrand is given the value `0` at `x = 0`, which does not affect the integral.) -/
