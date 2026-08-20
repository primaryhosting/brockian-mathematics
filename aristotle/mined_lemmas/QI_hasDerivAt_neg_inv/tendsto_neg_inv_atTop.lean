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


theorem tendsto_neg_inv_atTop {c : ℝ} : Tendsto (fun t : ℝ => -(c + t)⁻¹) atTop (𝓝 0) := by
  have : Tendsto (fun t : ℝ => c + t) atTop atTop := tendsto_atTop_add_const_left _ c tendsto_id
  simpa using (this.inv_tendsto_atTop).neg

/-- Integrability of the square of a resolvent. -/
