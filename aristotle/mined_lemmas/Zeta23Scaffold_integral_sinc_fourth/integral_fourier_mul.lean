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

lemma integral_fourier_mul (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ : ℝ, 𝓕 f ξ * g ξ = ∫ x : ℝ, f x * 𝓕 g x := by
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    exact real_inner_comm x y
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) (μ := volume)
    (ν := volume) Real.continuous_fourierChar continuous_inner hf hg
  rw [hflip] at h
  simpa [smul_eq_mul] using h

