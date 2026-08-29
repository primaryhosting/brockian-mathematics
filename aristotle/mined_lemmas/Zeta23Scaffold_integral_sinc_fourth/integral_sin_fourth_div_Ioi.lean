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

open MeasureTheory Set Real Filter Topology

/-! ### Laplace transform of `cos (a * x)` on `(0, ∞)` -/

/-- The function `x ↦ e^{-t x} cos (a x)` is integrable on `(0, ∞)` when `t > 0`. -/

theorem integral_sin_fourth_div_Ioi :
    ∫ x in Ioi (0 : ℝ), Real.sin x ^ 4 / x ^ 4 = π / 3 := by
  have hswap := MeasureTheory.integral_integral_swap
    (f := sincAux) sincAux_integrable_prod
  have hR : ∫ t in Ioi (0:ℝ), ∫ x in Ioi (0:ℝ), sincAux x t = 2 * π := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => 32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹)) ?_]
    · exact integral_lorentz_combo
    · intro t ht
      have htp : (0:ℝ) < t := ht
      show (∫ x in Ioi (0:ℝ), sincAux x t) = 32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹)
      rw [← integral_norm_sincAux t htp]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro x _
      show t ^ 3 * Real.sin x ^ 4 * Real.exp (-(x * t))
          = ‖t ^ 3 * Real.sin x ^ 4 * Real.exp (-(x * t))‖
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (pow_nonneg htp.le 3) (by positivity)) (Real.exp_nonneg _))]
  have hL : ∫ x in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), sincAux x t
      = 6 * ∫ x in Ioi (0:ℝ), Real.sin x ^ 4 / x ^ 4 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hx' : (0:ℝ) < x := hx
    show (∫ t in Ioi (0:ℝ), sincAux x t) = 6 * (Real.sin x ^ 4 / x ^ 4)
    have hrw : ∀ t : ℝ, sincAux x t = Real.sin x ^ 4 * (t ^ 3 * Real.exp (-(x * t))) := by
      intro t; unfold sincAux; ring
    simp only [hrw]
    rw [MeasureTheory.integral_const_mul, integral_cube_mul_exp x hx']
    field_simp
  rw [hL, hR] at hswap
  linarith [hswap]

/-- **The main result.** `∫_ℝ (sin x / x)⁴ dx = 2π/3`. -/
