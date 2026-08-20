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


theorem bkm_eq_sum (hω : ω.PosDef) (hΔ : Δ.IsHermitian) :
    bkm ω Δ = ∑ i, ∑ j, ‖cj hω Δ i j‖ ^ 2 *
      (∫ t in Ioi (0:ℝ), (eigV hω i + t)⁻¹ * (eigV hω j + t)⁻¹) := by
  unfold bkm
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => trace_res_quad_re hω (le_of_lt ht) hΔ)]
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => ?_)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_finset_sum _ (fun j _ => ?_)]
    · exact Finset.sum_congr rfl fun j _ => MeasureTheory.integral_const_mul _ _
    · exact ((integrableOn_resProd (eigV_pos hω i) (eigV_pos hω j)).const_mul _)
  · exact MeasureTheory.integrable_finset_sum _
      (fun j _ => ((integrableOn_resProd (eigV_pos hω i) (eigV_pos hω j)).const_mul _))

/-- Integrability in `t` of the BKM integrand. -/
