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

open scoped FourierTransform
open MeasureTheory Real Complex

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1,1]`. -/

lemma sinc_pi_sq_le (ξ : ℝ) : Real.sinc (π * ξ) ^ 2 ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
  have hpi : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hpos : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
  have hge : ξ ^ 2 ≤ (π * ξ) ^ 2 := by
    have : (0 : ℝ) ≤ ξ ^ 2 * (π ^ 2 - 1) := mul_nonneg (sq_nonneg ξ) (by nlinarith)
    nlinarith
  rcases le_or_gt ((π * ξ) ^ 2) 1 with h | h
  · have hx2 : ξ ^ 2 ≤ 1 := le_trans hge h
    have h1 : Real.sinc (π * ξ) ^ 2 ≤ 1 := by
      nlinarith [Real.abs_sinc_le_one (π * ξ), abs_nonneg (Real.sinc (π * ξ)),
        sq_abs (Real.sinc (π * ξ))]
    have h2 : (1 : ℝ) ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hpos]; linarith
    linarith
  · have hne : π * ξ ≠ 0 := by
      intro h0; rw [h0] at h; norm_num at h
    have hξ : ξ ≠ 0 := by
      intro h0; exact hne (by rw [h0, mul_zero])
    have hsq : Real.sinc (π * ξ) ^ 2 ≤ ((π * ξ) ^ 2)⁻¹ := by
      rw [Real.sinc_of_ne_zero hne, div_pow, div_le_iff₀ (by positivity),
        inv_mul_cancel₀ (by positivity)]
      nlinarith [Real.sin_sq_le_one (π * ξ)]
    have h3 : ((π * ξ) ^ 2)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      have heq : 2 * (1 + ξ ^ 2)⁻¹ - ((π * ξ) ^ 2)⁻¹
          = (2 * (π * ξ) ^ 2 - (1 + ξ ^ 2)) / ((1 + ξ ^ 2) * (π * ξ) ^ 2) := by
        have h1 : (1 : ℝ) + ξ ^ 2 ≠ 0 := by positivity
        have h2 : π ≠ 0 := Real.pi_ne_zero
        field_simp
      have hnum : 0 ≤ 2 * (π * ξ) ^ 2 - (1 + ξ ^ 2) := by linarith
      have hfin : 0 ≤ 2 * (1 + ξ ^ 2)⁻¹ - ((π * ξ) ^ 2)⁻¹ := by
        rw [heq]; positivity
      linarith
    linarith

