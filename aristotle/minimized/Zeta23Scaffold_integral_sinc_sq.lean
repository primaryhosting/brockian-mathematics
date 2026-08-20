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

lemma integrable_sinc_sq : Integrable (fun x : ℝ => Real.sinc x ^ 2) := by
  have hint : Integrable (fun x : ℝ => 2 * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 2
  refine hint.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [show (2 : ℝ) * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) by ring, le_div_iff₀ hpos]
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  · rw [Real.sinc_of_ne_zero hx]
    have h1 : Real.sin x ^ 2 ≤ x ^ 2 := by
      nlinarith [Real.abs_sin_le_abs (x := x), sq_abs x, sq_abs (Real.sin x),
        abs_nonneg (Real.sin x)]
    have h2 : Real.sin x ^ 2 ≤ 1 := by nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hx2]
    nlinarith
