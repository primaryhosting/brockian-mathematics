import Mathlib
/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Complex
open scoped FourierTransform

noncomputable section

namespace Zeta23Scaffold

/-- The tent function `t ↦ max (1 - |t|) 0`. -/

lemma integral_sinc_sq_eq_pi : ∫ x : ℝ, Real.sinc x ^ 2 = π := by
  have hinv := continuous_tent.fourierInv_fourier_eq integrable_tent integrable_fourier_tent
  have h0 : 𝓕⁻ (𝓕 tent) 0 = ∫ ξ : ℝ, 𝓕 tent ξ := by
    rw [Real.fourierInv_eq']
    simp
  have h1 : (∫ ξ : ℝ, 𝓕 tent ξ) = 1 := by
    rw [← h0, hinv]
    simp [tent, tentR, abs_zero]
  have h2 : (∫ ξ : ℝ, Real.sinc (π * ξ) ^ 2) = 1 := by
    have : (∫ ξ : ℝ, ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ)) = 1 := by
      rw [← h1]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => (fourier_tent ξ).symm)
    rw [_root_.integral_complex_ofReal] at this
    exact_mod_cast this
  rw [MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => Real.sinc x ^ 2) π] at h2
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ π⁻¹), smul_eq_mul] at h2
  field_simp at h2
  linarith

/-- The normalization integral of the sine kernel: `∫ (sin x / x)^2 dx = π`. -/
