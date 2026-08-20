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

lemma sinc_sq_le (t : ℝ) : Real.sinc t ^ 2 ≤ 2 * (1 + t^2)⁻¹ := by
  have hpos : (0:ℝ) < 1 + t^2 := by positivity
  rcases eq_or_ne t 0 with rfl | ht
  · norm_num
  · rw [Real.sinc_of_ne_zero ht, div_pow]
    have h1 : Real.sin t ^ 2 ≤ t^2 := by
      have := Real.abs_sin_le_abs (x := t)
      nlinarith [abs_nonneg (Real.sin t), abs_nonneg t, sq_abs (Real.sin t), sq_abs t]
    have h2 : Real.sin t ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (Real.cos t)]
    have ht2 : (0:ℝ) < t^2 := by positivity
    have heq : 2 * (1 + t^2)⁻¹ = (2*t^2)/(1+t^2)/t^2 := by field_simp
    rw [heq, div_le_div_iff_of_pos_right ht2, le_div_iff₀ hpos]
    nlinarith

