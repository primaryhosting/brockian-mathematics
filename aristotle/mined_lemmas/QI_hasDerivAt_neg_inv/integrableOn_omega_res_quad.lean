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


theorem integrableOn_omega_res_quad (hω : ω.PosDef) (Δ : Mat n) :
    IntegrableOn (fun t : ℝ => (ω * res ω t * Δ * res ω t).trace.re) (Ioi 0) := by
  refine MeasureTheory.IntegrableOn.congr_fun ?_
    (fun t ht => (trace_omega_res_quad_re hω (le_of_lt ht) Δ).symm) measurableSet_Ioi
  refine MeasureTheory.integrable_finset_sum _ (fun i _ => ?_)
  exact (((integrableOn_resSq (eigV_pos hω i)).const_mul (eigV hω i)).const_mul _)

/-- `∫₀^∞ Tr (ω R Δ R) dt = Tr Δ`. -/
