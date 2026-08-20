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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem integrableOn_resSq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (c + t)⁻¹ * (c + t)⁻¹) (Ioi 0) := by
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (g := fun t : ℝ => -(c + t)⁻¹) (l := 0)
    (continuousWithinAt_neg_inv hc) (fun t ht => hasDerivAt_neg_inv hc (le_of_lt ht))
    (fun t ht => ?_) tendsto_neg_inv_atTop
  have : 0 < c + t := by simp only [mem_Ioi] at ht; linarith
  positivity

/-- `∫₀^∞ c/(c+t)² dt = 1`. -/
