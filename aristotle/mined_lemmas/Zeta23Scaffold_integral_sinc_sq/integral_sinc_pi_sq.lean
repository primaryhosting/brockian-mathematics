import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Real
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function. -/

lemma integral_sinc_pi_sq : ∫ w : ℝ, (Real.sin (π * w) / (π * w)) ^ 2 = 1 := by
  have hFint : Integrable (𝓕 tri) :=
    integrable_sinc_pi_sq.ofReal.congr fourier_tri_ae.symm
  have h0 : 𝓕⁻ (𝓕 tri) 0 = tri 0 :=
    tri_integrable.fourierInv_fourier_eq hFint tri_continuous.continuousAt
  have h1 : 𝓕⁻ (𝓕 tri) 0 = ∫ w : ℝ, 𝓕 tri w := by
    rw [Real.fourierInv_eq']
    simp
  have h2 : tri 0 = 1 := by simp [tri]
  have h3 : ∫ w : ℝ, 𝓕 tri w = ((∫ w : ℝ, (Real.sin (π * w) / (π * w)) ^ 2 : ℝ) : ℂ) := by
    rw [integral_congr_ae fourier_tri_ae, integral_complex_ofReal]
  rw [h1, h2, h3] at h0
  exact_mod_cast h0

/-- The squared sine kernel `x ↦ (sin x / x)²` is Lebesgue integrable on `ℝ`. -/
