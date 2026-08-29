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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform Complex intervalIntegral

/-- The tent (triangle) function `max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma integrable_fourier_tent : Integrable (𝓕 tent) := by
  have hrw : 𝓕 tent = fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) := funext fourier_tent
  rw [hrw]
  apply Integrable.ofReal
  have hg : Integrable (fun ξ : ℝ => 2 * (1 + ξ ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul 2
  apply Integrable.mono' hg
  · exact ((Real.continuous_sinc.comp (by fun_prop)).pow 2).aestronglyMeasurable
  · filter_upwards with ξ
    show ‖Real.sinc (π * ξ) ^ 2‖ ≤ 2 * (1 + ξ ^ 2)⁻¹
    have h1 : Real.sinc (π * ξ) ^ 2 ≤ 2 / (1 + (π * ξ) ^ 2) := sinc_sq_le _
    have h2 : (0 : ℝ) ≤ Real.sinc (π * ξ) ^ 2 := sq_nonneg _
    have hpi : (1 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    have h3 : (1 : ℝ) + ξ ^ 2 ≤ 1 + (π * ξ) ^ 2 := by
      rw [mul_pow]; nlinarith [sq_nonneg ξ]
    have h4 : 2 / (1 + (π * ξ) ^ 2) ≤ 2 / (1 + ξ ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h3
    have h5 : 2 * (1 + ξ ^ 2)⁻¹ = 2 / (1 + ξ ^ 2) := by ring
    rw [Real.norm_of_nonneg h2, h5]
    linarith

/-- `∫ (tent)² = 2/3`. -/
