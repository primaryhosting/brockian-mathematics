import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform intervalIntegral

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma sinc_sq_le (y : ℝ) : Real.sinc y ^ 2 ≤ 2 * (1 + y ^ 2)⁻¹ := by
  rcases le_or_gt |y| 1 with h | h
  · have h1 : Real.sinc y ^ 2 ≤ 1 := by
      have := Real.abs_sinc_le_one y
      nlinarith [abs_nonneg (Real.sinc y), sq_abs (Real.sinc y)]
    have h2 : (1:ℝ) ≤ 2 * (1 + y ^ 2)⁻¹ := by
      have hy : y ^ 2 ≤ 1 := by nlinarith [sq_abs y, abs_nonneg y]
      rw [le_mul_inv_iff₀ (by positivity)]
      linarith
    linarith
  · have hy0 : y ≠ 0 := by
      intro h0; rw [h0] at h; simp at h; linarith
    have hs : Real.sinc y ^ 2 ≤ (y ^ 2)⁻¹ := by
      rw [Real.sinc_of_ne_zero hy0, div_pow]
      have h1 : Real.sin y ^ 2 ≤ 1 := by
        nlinarith [Real.neg_one_le_sin y, Real.sin_le_one y]
      have hy2 : 0 < y ^ 2 := by positivity
      rw [div_le_iff₀ hy2, inv_mul_cancel₀ hy2.ne']
      linarith
    have h2 : (y ^ 2)⁻¹ ≤ 2 * (1 + y ^ 2)⁻¹ := by
      have hy2 : 1 < y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
      rw [inv_le_iff_one_le_mul₀ (by linarith), mul_assoc, mul_comm ((1 + y ^ 2)⁻¹) (y ^ 2),
        ← mul_assoc, le_mul_inv_iff₀ (show (0:ℝ) < 1 + y ^ 2 by positivity)]
      linarith
    linarith

