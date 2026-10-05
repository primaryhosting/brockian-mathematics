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

theorem integral_windowFun {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0 : ℝ)..1, windowFun a b t) = b - a := by
  have : (∫ t in (0 : ℝ)..1, windowFun a b t)
      = (∫ t in (0 : ℝ)..1, stepFun a t) - ∫ t in (0 : ℝ)..1, stepFun b t :=
    intervalIntegral.integral_sub (intervalIntegrable_stepFun a) (intervalIntegrable_stepFun b)
  rw [this, integral_stepFun ha (hab.trans hb), integral_stepFun (ha.trans hab) hb]
  ring

