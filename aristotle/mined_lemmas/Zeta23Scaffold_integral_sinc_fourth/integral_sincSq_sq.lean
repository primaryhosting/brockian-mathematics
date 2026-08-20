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

lemma integral_sincSq_sq : ∫ ξ : ℝ, sincSq ξ ^ 2 = 2/3 := by
  have h := integral_fourier_mul tentC (fun ξ : ℝ => (sincSq ξ : ℂ))
    tentC_integrable sincSqC_integrable
  rw [fourier_tentC, fourier_sincSqC] at h
  have hL : ∫ ξ : ℝ, ((sincSq ξ : ℂ) * (sincSq ξ : ℂ))
      = ((∫ ξ : ℝ, sincSq ξ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext ξ
    push_cast
    ring
  have hR : ∫ x : ℝ, (tentC x * tentC x) = ((∫ x : ℝ, tent x ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    simp only [tentC]
    push_cast
    ring
  rw [hL, hR, integral_tent_sq] at h
  exact_mod_cast h

/-! ### The main theorem -/

/-- **The fourth-power sinc integral**: `∫_ℝ (sin x / x)⁴ dx = 2π/3`. -/
