/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The normalization integral of the sine kernel,
`∫ x : ℝ, (sin x / x) ^ 2 = π`.

The proof computes the Fourier transform of the triangle function
`tri x = max (1 - |x|) 0`, which is `w ↦ sinc (π w) ^ 2`, and then applies the
Fourier inversion formula at `0`.

Note that in Lean `sin 0 / 0 = 0`, so the integrand of the main statement differs from the
continuous extension `sinc` only on the null set `{0}`; the value of the integral is unaffected.
-/

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Zeta23Scaffold

/-- The triangle function `x ↦ max (1 - |x|) 0`, viewed as a complex-valued function on `ℝ`. -/

lemma integrable_sinc_sq : Integrable (fun x : ℝ => Real.sinc x ^ 2) := by
  have hg : Integrable (fun x : ℝ => 2 * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 2
  refine Integrable.mono' hg (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  rcases le_or_gt |x| 1 with h | h
  · have h1 : Real.sinc x ^ 2 ≤ 1 := by
      nlinarith [abs_le.1 (Real.abs_sinc_le_one x)]
    have h2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    have : (1:ℝ) ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]; linarith
    linarith
  · have hx : x ≠ 0 := by rintro rfl; simp at h; linarith
    have hs : Real.sinc x ^ 2 ≤ (x ^ 2)⁻¹ := by
      rw [Real.sinc_of_ne_zero hx, div_pow]
      have : Real.sin x ^ 2 ≤ 1 := by nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]
      rw [div_le_iff₀ (by positivity), inv_mul_cancel₀ (by positivity)]
      exact this
    have h2 : 1 < x ^ 2 := by nlinarith [sq_abs x]
    have : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ (by positivity), mul_comm, ← mul_assoc,
        le_mul_inv_iff₀ (by positivity)]
      linarith
    linarith

/-- Splitting the integral of `exp (c * v) * tri v` into the two halves of the triangle. -/
