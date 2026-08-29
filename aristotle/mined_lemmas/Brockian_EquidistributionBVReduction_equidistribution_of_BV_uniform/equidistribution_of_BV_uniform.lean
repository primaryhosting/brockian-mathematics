import Mathlib

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

import Mathlib

/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Brockian.EquidistributionBVReduction

/-- The (right-continuous) step function jumping from `0` to `1` at `c`. -/

theorem equidistribution_of_BV_uniform (x : ℕ → ℝ) (h : BVAverageConvergence x) :
    EquidistributedMod1 x := by
  intro a b ha hab hb
  have key := h (windowFun a b) (boundedVariationOn_windowFun a b)
    (intervalIntegrable_windowFun a b)
  rw [integral_windowFun ha hab hb] at key
  simpa only [sum_windowFun hab x] using key

end Brockian.EquidistributionBVReduction

