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

theorem sincAux_integrableOn_x (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => sincAux x t) (Ioi 0) := by
  apply MeasureTheory.Integrable.mono' ((exp_neg_integrableOn_Ioi 0 ht).const_mul (t ^ 3))
  · apply Continuous.aestronglyMeasurable
    unfold sincAux
    fun_prop
  · filter_upwards with x
    unfold sincAux
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), show -(x * t) = -t * x by ring]
    calc t ^ 3 * Real.sin x ^ 4 * Real.exp (-t * x) ≤ t ^ 3 * 1 * Real.exp (-t * x) := by
          gcongr
          exact sin_pow_four_le_one x
      _ = t ^ 3 * Real.exp (-t * x) := by ring

