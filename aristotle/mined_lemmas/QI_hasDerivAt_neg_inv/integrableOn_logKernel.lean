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


theorem integrableOn_logKernel {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (1 + t)⁻¹ - (a + t)⁻¹) (Ioi 0) := by
  refine MeasureTheory.IntegrableOn.congr_fun
    ((integrableOn_resProd one_pos ha).const_mul (a - 1)) ?_ measurableSet_Ioi
  intro t ht
  simp only [mem_Ioi] at ht
  have h1 : (1 : ℝ) + t ≠ 0 := by positivity
  have h2 : a + t ≠ 0 := by positivity
  field_simp
  ring

/-- `∫₀^∞ (1/(1+t) - 1/(a+t)) dt = log a`. -/
