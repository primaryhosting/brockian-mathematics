import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-- Explicit antiderivative computation: the interval integral of a linear function times a
complex exponential. -/

lemma integral_sincSqC_sq : ∫ ξ : ℝ, sincSqC ξ * sincSqC ξ = (2 / 3 : ℂ) := by
  have hflip : ∫ ξ : ℝ, (𝓕 tentC ξ) * (sincSqC ξ) = ∫ x : ℝ, (tentC x) * (𝓕 sincSqC x) := by
    simpa [mul_comm] using (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner integrable_tentC integrable_sincSqC)
  rw [fourier_tentC] at hflip
  rw [hflip, fourier_sincSqC, integral_tentC_sq]

