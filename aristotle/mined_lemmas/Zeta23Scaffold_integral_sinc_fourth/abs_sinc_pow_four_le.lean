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

lemma abs_sinc_pow_four_le (t : ℝ) : |Real.sinc t ^ 4| ≤ 2 * (1 + t ^ 2)⁻¹ := by
  have hpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  rw [abs_pow]
  rcases le_or_gt |t| 1 with h | h
  · have h1 : |Real.sinc t| ^ 4 ≤ 1 := by
      calc |Real.sinc t| ^ 4 ≤ 1 ^ 4 :=
            pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one t) 4
        _ = 1 := one_pow 4
    have h2 : (1:ℝ) ≤ 2 * (1 + t ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hpos]
      nlinarith [sq_abs t, abs_nonneg t]
    linarith
  · have ht : t ≠ 0 := by
      intro h0; rw [h0] at h; simp at h; linarith
    have hta : (0:ℝ) < |t| := abs_pos.mpr ht
    have hs : |Real.sinc t| ≤ |t|⁻¹ := by
      rw [Real.sinc_of_ne_zero ht, abs_div, div_le_iff₀ hta, inv_mul_cancel₀ hta.ne']
      exact Real.abs_sin_le_one t
    have h1 : |Real.sinc t| ^ 4 ≤ (|t|⁻¹) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hs 4
    have h2 : (|t|⁻¹) ^ 4 ≤ 2 * (1 + t ^ 2)⁻¹ := by
      rw [show ((|t|⁻¹ : ℝ)) ^ 4 = 1 / |t| ^ 4 by rw [inv_pow]; ring,
        show (2:ℝ) * (1 + t ^ 2)⁻¹ = 2 / (1 + t ^ 2) by ring,
        div_le_div_iff₀ (by positivity) hpos, ← sq_abs t]
      have ha2 : 1 < |t| ^ 2 := by nlinarith
      nlinarith [ha2]
    linarith

