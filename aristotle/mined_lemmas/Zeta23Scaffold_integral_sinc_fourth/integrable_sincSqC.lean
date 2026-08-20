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

lemma integrable_sincSqC : Integrable sincSqC := by
  have hbound : ∀ ξ : ℝ, ‖sincSqC ξ‖ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    have h1 : ‖sincSqC ξ‖ = Real.sinc (π * ξ) ^ 2 := by
      simp [sincSqC, Complex.norm_real]
    rw [h1]
    have hle1 : Real.sinc (π * ξ) ^ 2 ≤ 1 := by
      have := Real.abs_sinc_le_one (π * ξ)
      nlinarith [abs_nonneg (Real.sinc (π * ξ)), sq_abs (Real.sinc (π * ξ))]
    have hpos : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
    rw [show (2 : ℝ) * (1 + ξ ^ 2)⁻¹ = 2 / (1 + ξ ^ 2) by ring, le_div_iff₀ hpos]
    rcases eq_or_ne ξ 0 with rfl | hξ
    · norm_num
    · have hpx : π * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
      have h2 : Real.sinc (π * ξ) ^ 2 * (π * ξ) ^ 2 = Real.sin (π * ξ) ^ 2 := by
        rw [Real.sinc_of_ne_zero hpx]; field_simp
      have h3 : Real.sinc (π * ξ) ^ 2 * (π * ξ) ^ 2 ≤ 1 := by
        rw [h2]; nlinarith [Real.neg_one_le_sin (π * ξ), Real.sin_le_one (π * ξ)]
      have hπ : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
      have hξ2 : (0 : ℝ) < ξ ^ 2 := by positivity
      have hs : (0 : ℝ) ≤ Real.sinc (π * ξ) ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hs hξ2.le, mul_le_mul_of_nonneg_right hπ (mul_nonneg hs hξ2.le)]
  refine Integrable.mono' (g := fun ξ : ℝ => 2 * (1 + ξ ^ 2)⁻¹) ?_
    continuous_sincSqC.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  simpa using (integrable_inv_one_add_sq).const_mul 2

