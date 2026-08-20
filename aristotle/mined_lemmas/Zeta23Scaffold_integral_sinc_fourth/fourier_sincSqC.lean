import Mathlib
/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The proof follows the classical Fourier-analytic route.  Writing `Λ` for the tent function
`Λ x = max (1 - |x|) 0`, an elementary computation gives `𝓕 Λ ξ = (sin (π ξ) / (π ξ))²`.
Fourier inversion then gives `𝓕 ((sin (π ·) / (π ·))²) = Λ`, and the multiplication formula
`∫ 𝓕 f · g = ∫ f · 𝓕 g` yields
`∫ (sin (π ξ) / (π ξ))⁴ dξ = ∫ Λ² = 2/3`.
Rescaling `x = π ξ` produces `∫ (sin x / x)⁴ dx = 2 π / 3`.
-/

open MeasureTheory Real Complex intervalIntegral
open scoped FourierTransform

namespace Zeta23Scaffold

/-! ### The tent function and the squared sinc -/

/-- The tent (triangle) function `x ↦ max (1 - |x|) 0`. -/

lemma fourier_sincSqC : (𝓕 fun ξ : ℝ => (sincSq ξ : ℂ)) = tentC := by
  have hinv : 𝓕⁻ (𝓕 tentC) = tentC :=
    Continuous.fourierInv_fourier_eq tentC_continuous tentC_integrable
      (by rw [fourier_tentC]; exact sincSqC_integrable)
  funext x
  rw [← fourier_tentC]
  have hx := Real.fourierInv_eq_fourier_neg (𝓕 tentC) (-x)
  rw [neg_neg] at hx
  rw [← hx, hinv]
  simp [tentC, tent_neg]

/-! ### The Plancherel-type multiplication formula -/

