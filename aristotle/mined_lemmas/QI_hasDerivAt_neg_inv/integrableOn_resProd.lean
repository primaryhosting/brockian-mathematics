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


theorem integrableOn_resProd {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (a + t)⁻¹ * (b + t)⁻¹) (Ioi 0) := by
  set c := min a b with hc
  have hc0 : 0 < c := lt_min ha hb
  refine MeasureTheory.Integrable.mono' (integrableOn_resSq hc0) ?_ ?_
  · exact ((measurable_const.add measurable_id).inv.mul
      (measurable_const.add measurable_id).inv).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    have hat : 0 < a + t := by linarith
    have hbt : 0 < b + t := by linarith
    have hct : 0 < c + t := by linarith [lt_min ha hb]
    have h1 : c + t ≤ a + t := by simp [hc]
    have h2 : c + t ≤ b + t := by simp [hc]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr

/-- Integrability of `t ↦ (1+t)⁻¹ - (a+t)⁻¹` on `(0, ∞)`. -/
