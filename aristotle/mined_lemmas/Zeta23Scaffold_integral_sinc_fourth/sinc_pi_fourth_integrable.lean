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

lemma sinc_pi_fourth_integrable : Integrable (fun ξ : ℝ => Real.sinc (π * ξ) ^ 4) := by
  have hg : Integrable (fun ξ : ℝ => 2 * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 2
  apply Integrable.mono' hg
  · exact ((Real.continuous_sinc.comp
      (continuous_const.mul continuous_id)).pow 4).aestronglyMeasurable
  · filter_upwards with ξ
    have h1 := abs_sinc_pow_four_le (π * ξ)
    have h2 : 2 * (1 + (π * ξ) ^ 2)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
      have hp : (1:ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
      have hle : (1:ℝ) + ξ ^ 2 ≤ 1 + (π * ξ) ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ π ^ 2 - 1) (sq_nonneg ξ)]
      have h3 : (0:ℝ) < 1 + ξ ^ 2 := by positivity
      gcongr
    simp only [Real.norm_eq_abs]
    linarith

