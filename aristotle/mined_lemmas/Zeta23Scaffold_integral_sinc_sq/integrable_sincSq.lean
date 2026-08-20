import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Filter intervalIntegral
open scoped FourierTransform Topology Real

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma integrable_sincSq : Integrable (fun x : ℝ => (Real.sinc x) ^ 2) := by
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul 2)
  · exact (Real.continuous_sinc.pow 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : Real.sinc x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (Real.abs_sinc_le_one x)
    have hp : (0:ℝ) < 1 + x^2 := by positivity
    rcases le_or_gt (x^2) 1 with h | h
    · rw [← div_eq_mul_inv, le_div_iff₀ hp]
      nlinarith
    · have hx2 : (0:ℝ) < x^2 := by linarith
      have h2 : Real.sinc x ^ 2 ≤ 1 / x^2 := by
        have hx : x ≠ 0 := by intro h0; rw [h0] at hx2; simp at hx2
        rw [Real.sinc_of_ne_zero hx, div_pow]
        gcongr
        exact Real.sin_sq_le_one x
      refine h2.trans ?_
      rw [← div_eq_mul_inv, div_le_div_iff₀ hx2 hp]
      nlinarith

