/-
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The header above is repeated as a plain comment on the first line of this file, since Lean 4
requires `import` commands to precede any module docstring.

## Method

With `T u = max 0 (1 - |u|)` the tent function, an explicit computation gives
`𝓕 T ξ = sinc (π ξ) ^ 2`.  The convolution theorem then yields `𝓕 (T ⋆ T) ξ = sinc (π ξ) ^ 4`,
and Fourier inversion at `0` gives
`∫ sinc (π ξ) ^ 4 dξ = (T ⋆ T) 0 = ∫ T ² = 2/3`.
Rescaling by `π` produces `∫ (sin x / x) ^ 4 dx = 2π/3`.
-/

open MeasureTheory Convolution FourierTransform
open scoped Real

namespace Zeta23Scaffold

/-- The tent (triangle) function `u ↦ max 0 (1 - |u|)`. -/

lemma fourier_tentC (ξ : ℝ) : 𝓕 tentC ξ = ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := by
  have hF : 𝓕 tentC ξ = ∫ v : ℝ, Complex.exp ((-(2 * π * ξ) * Complex.I) * v) * tentC v := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [RCLike.inner_apply, conj_trivial, Circle.smul_def, Real.fourierChar_apply,
      smul_eq_mul]
    push_cast
    ring_nf
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [hF]
    simpa using integral_tentC
  · set c : ℂ := -(2 * (π:ℂ) * (ξ:ℂ)) * Complex.I with hcdef
    have hy : (π * ξ) ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
    have hyC : ((π:ℂ) * (ξ:ℂ)) ≠ 0 := by simpa using Complex.ofReal_ne_zero.mpr hy
    have hc : c ≠ 0 := by
      simp only [hcdef]
      exact mul_ne_zero (by simpa using hyC) Complex.I_ne_zero
    have hsum : Complex.exp c + Complex.exp (-c) = ((2 * Real.cos (2 * π * ξ) : ℝ) : ℂ) := by
      have h1 : (-(2 * (π:ℂ) * (ξ:ℂ))) = ((-(2 * π * ξ) : ℝ) : ℂ) := by push_cast; ring
      have h2 : -(((-(2 * π * ξ) : ℝ) : ℂ) * Complex.I) = (((2 * π * ξ) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hcdef, h1, Complex.exp_mul_I, h2, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sin]
      push_cast [Real.cos_neg, Real.sin_neg]
      ring
    rw [hF, integral_exp_mul_tentC c hc, hsum, Real.sinc_of_ne_zero hy, hcdef]
    have hcos : Real.cos (2 * π * ξ) = 1 - 2 * Real.sin (π * ξ) ^ 2 := by
      have h : (2:ℝ) * π * ξ = 2 * (π * ξ) := by ring
      rw [h, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (π * ξ)]
    rw [hcos]
    have hI : (-(2 * (π:ℂ) * (ξ:ℂ)) * Complex.I) ^ 2 = -(4 * ((π:ℂ) * (ξ:ℂ)) ^ 2) := by
      have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
      ring_nf
      rw [hI2]
      ring
    rw [hI]
    push_cast
    field_simp
    ring

/-- The self-convolution of the tent function. -/
