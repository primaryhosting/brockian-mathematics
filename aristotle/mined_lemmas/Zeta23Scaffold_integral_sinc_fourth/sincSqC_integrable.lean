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

lemma sincSqC_integrable : Integrable (fun ξ : ℝ => (sincSq ξ : ℂ)) := by
  have hg : Integrable (fun ξ : ℝ => 2 * (1 + (π*ξ)^2)⁻¹) := by
    apply Integrable.const_mul
    exact (integrable_comp_mul_left_iff (fun x : ℝ => (1+x^2)⁻¹) Real.pi_ne_zero).2
      integrable_inv_one_add_sq
  apply Integrable.mono' hg
  · exact (Complex.continuous_ofReal.comp sincSq_continuous).aestronglyMeasurable
  · filter_upwards with ξ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sincSq_nonneg ξ)]
    exact sinc_sq_le _

/-- The Fourier transform of the squared sinc is the tent function (Fourier inversion). -/
