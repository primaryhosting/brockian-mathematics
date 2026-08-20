import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Real
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function. -/

lemma sinc_sq_le (w : ℝ) : (Real.sin (π * w) / (π * w)) ^ 2 ≤ 2 * (1 + w ^ 2)⁻¹ := by
  rcases eq_or_ne w 0 with rfl | hw
  · norm_num
  · have hpos : (0 : ℝ) < 1 + w ^ 2 := by positivity
    set t : ℝ := π * w with ht
    have hts : t ≠ 0 := mul_ne_zero Real.pi_ne_zero hw
    have ht2 : 0 < t ^ 2 := by positivity
    have h1 : Real.sin t ^ 2 ≤ 1 := by nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t]
    have h2 : Real.sin t ^ 2 ≤ t ^ 2 := by
      have h := abs_sin_le_abs (x := t)
      nlinarith [abs_nonneg t, abs_nonneg (Real.sin t), sq_abs t, sq_abs (Real.sin t)]
    have hteq : t ^ 2 = π ^ 2 * w ^ 2 := by rw [ht]; ring
    have hpi : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    have hw2 : w ^ 2 ≤ t ^ 2 := by rw [hteq]; nlinarith [sq_nonneg w]
    have key : (1 + w ^ 2) * Real.sin t ^ 2 ≤ 2 * t ^ 2 := by nlinarith
    rw [div_pow, div_le_iff₀ ht2]
    have heq : 2 * (1 + w ^ 2)⁻¹ * t ^ 2 = 2 * t ^ 2 / (1 + w ^ 2) := by field_simp
    rw [heq, le_div_iff₀ hpos]
    nlinarith

