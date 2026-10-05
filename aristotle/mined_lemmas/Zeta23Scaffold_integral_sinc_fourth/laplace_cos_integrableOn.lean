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

theorem laplace_cos_integrableOn (t a : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => Real.exp (-(t * x)) * Real.cos (a * x)) (Ioi 0) := by
  apply MeasureTheory.Integrable.mono' (exp_neg_integrableOn_Ioi 0 ht)
  · exact ((Real.continuous_exp.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, neg_mul]
    calc ‖Real.exp (-(t * x))‖ * ‖Real.cos (a * x)‖ ≤ ‖Real.exp (-(t * x))‖ * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = Real.exp (-(t * x)) := by simp [Real.exp_pos, abs_of_pos]

/-- The Laplace transform of the cosine: `∫_0^∞ e^{-t x} cos (a x) dx = t / (t² + a²)`. -/
