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

theorem integral_cube_mul_exp (x : ℝ) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t ^ 3 * Real.exp (-(x * t)) = 6 / x ^ 4 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 4) (r := x) (by norm_num) hx
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (f := fun t : ℝ => t ^ ((4 : ℝ) - 1) * Real.exp (-(x * t)))
    (g := fun t : ℝ => t ^ 3 * Real.exp (-(x * t))) ?_] at h
  · rw [h]
    have hg : Real.Gamma 4 = 6 := by
      have h3 := Real.Gamma_nat_eq_factorial 3
      norm_num at h3
      convert h3 using 2
      norm_num
    rw [hg]
    have hpow : ((1 : ℝ) / x) ^ (4 : ℝ) = (1 / x) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast (1 / x) 4]; norm_num
    rw [hpow]
    field_simp
  · intro t _
    simp only
    congr 1
    rw [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-! ### The Lorentzian integrals -/

