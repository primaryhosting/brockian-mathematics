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

theorem integral_norm_sincAux (t : ℝ) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), ‖sincAux x t‖
      = 32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹) := by
  have hcongr : ∀ x ∈ Ioi (0 : ℝ),
      ‖sincAux x t‖ = t ^ 3 * (Real.sin x ^ 4 * Real.exp (-(t * x))) := by
    intro x _
    unfold sincAux
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), show -(x * t) = -(t * x) by ring]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
    MeasureTheory.integral_const_mul, laplace_sin_fourth t ht, cube_mul_laplace_sin_fourth t ht]

