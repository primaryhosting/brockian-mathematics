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

lemma fourier_tri (w : ℝ) : 𝓕 tri w = ((Real.sinc (π * w) ^ 2 : ℝ) : ℂ) := by
  have hrw : 𝓕 tri w = ∫ v : ℝ, Complex.exp ((-(2 * π * w : ℝ) * Complex.I) * v) * tri v := by
    rw [Real.fourier_real_eq]
    simp only [Real.fourierChar_apply, Circle.smul_def, smul_eq_mul]
    congr 1 with v
    congr 2
    push_cast
    ring
  rw [hrw, integral_exp_mul_tri]
  rcases eq_or_ne w 0 with rfl | hw
  · have e1 : ∫ v in (-1:ℝ)..0, (1 + (v:ℂ)) * Complex.exp ((-(2*π*0 : ℝ) * Complex.I) * v)
        = ((∫ v in (-1:ℝ)..0, (1 + v) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun x _ => ?_
      push_cast
      simp
    have e2 : ∫ v in (0:ℝ)..1, (1 - (v:ℂ)) * Complex.exp ((-(2*π*0 : ℝ) * Complex.I) * v)
        = ((∫ v in (0:ℝ)..1, (1 - v) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun x _ => ?_
      push_cast
      simp
    rw [e1, e2]
    have h1 : ∫ v in (-1:ℝ)..0, (1 + v) = (1:ℝ)/2 := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      norm_num
    have h2 : ∫ v in (0:ℝ)..1, (1 - v) = (1:ℝ)/2 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      norm_num
    rw [h1, h2]
    norm_num
  · set c : ℂ := -(2 * π * w : ℝ) * Complex.I with hcdef
    have hpi := Real.pi_ne_zero
    have hpw : (π * w) ≠ 0 := mul_ne_zero hpi hw
    have hc : c ≠ 0 := by
      rw [hcdef]
      refine mul_ne_zero ?_ Complex.I_ne_zero
      simp only [neg_ne_zero, ne_eq, Complex.ofReal_eq_zero]
      exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) hw
    rw [integral_left_half c hc, integral_right_half c hc]
    have hsum : (1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2)
        + (Complex.exp c / c ^ 2 - 1 / c - 1 / c ^ 2)
        = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
      field_simp
      ring
    rw [hsum]
    have hcos : Complex.exp c + Complex.exp (-c) = 2 * (Real.cos (2 * π * w) : ℂ) := by
      rw [hcdef, Complex.ofReal_cos, Complex.cos]
      ring_nf
    have hcsq : c ^ 2 = -(((2 * π * w : ℝ)) : ℂ) ^ 2 := by
      rw [hcdef]; ring_nf; simp [Complex.I_sq]
    have h2 : (Real.cos (2 * π * w) : ℂ) = 1 - 2 * (Real.sin (π * w) : ℂ) ^ 2 := by
      have h : Real.cos (2 * π * w) = 1 - 2 * Real.sin (π * w) ^ 2 := by
        have h1 := Real.cos_two_mul (π * w)
        have h2 := Real.sin_sq_add_cos_sq (π * w)
        rw [show 2 * π * w = 2 * (π * w) by ring, h1]; nlinarith
      rw [h]; push_cast; ring
    rw [Real.sinc_of_ne_zero hpw, hcos, hcsq, h2]
    push_cast
    field_simp
    ring

/-- The Fourier transform of the triangle function is integrable. -/
