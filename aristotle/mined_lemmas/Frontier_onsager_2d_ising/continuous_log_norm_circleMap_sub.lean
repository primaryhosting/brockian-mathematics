/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The 2D Ising model on a finite torus -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

theorem continuous_log_norm_circleMap_sub (c : ℂ) (hc : ‖c‖ ≠ 1) :
    Continuous fun θ : ℝ => Real.log ‖circleMap 0 1 θ - c‖ := by
  refine Continuous.log (((continuous_circleMap 0 1).sub continuous_const).norm) ?_
  intro θ
  simp only [ne_eq, norm_eq_zero, sub_eq_zero]
  intro h
  exact hc (by rw [← h]; simp)

/-- The circle-average computation: `∫₀^{2π} log ‖e^{iθ} - c‖ dθ = 2π log⁺ ‖c‖`.
This is Mathlib's `circleAverage_log_norm_sub_const_eq_posLog` (Jensen formula file). -/
