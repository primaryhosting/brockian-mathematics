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


theorem continuousWithinAt_neg_inv {c : ℝ} (hc : 0 < c) :
    ContinuousWithinAt (fun t : ℝ => -(c + t)⁻¹) (Ici 0) 0 := by
  apply ContinuousAt.continuousWithinAt
  refine ((continuousAt_const.add continuousAt_id).inv₀ ?_).neg
  simpa using hc.ne'

