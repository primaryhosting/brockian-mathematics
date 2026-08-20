/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
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

/-! ## Space-time partial derivatives

We work with real functions `f : ℝ → ℝ → ℝ` of a time variable and a (one dimensional)
space variable. -/

/-- Partial derivative in the time variable. -/

theorem dx_dx_heatKernel {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dx (dx heatKernel) t x = heatKernel t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  have key : (fun y : ℝ => dx heatKernel t y)
      = fun y : ℝ => heatKernel t y * (-(y / (2 * t))) := by
    funext y
    exact dx_heatKernel ht y
  have hu := hasDerivAt_heatKernel_space ht x
  have hv : HasDerivAt (fun y : ℝ => -(y / (2 * t))) (-(1 / (2 * t))) x := by
    simpa using ((hasDerivAt_id x).div_const (2 * t)).neg
  have hmul : HasDerivAt (fun y : ℝ => heatKernel t y * -(y / (2 * t)))
      (heatKernel t x * -(x / (2 * t)) * -(x / (2 * t)) + heatKernel t x * -(1 / (2 * t))) x :=
    hu.mul hv
  have htne : t ≠ 0 := ne_of_gt ht
  rw [dx_apply, key, hmul.deriv]
  field_simp
  ring

