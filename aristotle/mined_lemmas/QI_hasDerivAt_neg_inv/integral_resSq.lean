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


theorem integral_resSq {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0:ℝ), c * ((c + t)⁻¹ * (c + t)⁻¹) = 1 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun t : ℝ => c * -(c + t)⁻¹) (f' := fun t : ℝ => c * ((c + t)⁻¹ * (c + t)⁻¹))
    (a := 0) (m := 0) ((continuousWithinAt_neg_inv hc).const_smul c)
    (fun t ht => (hasDerivAt_neg_inv hc (le_of_lt ht)).const_mul c)
    ((integrableOn_resSq hc).const_mul c)
    (by simpa using (tendsto_neg_inv_atTop (c := c)).const_mul c)
  rw [h]
  field_simp
  ring

/-- Integrability of the product of two resolvents. -/
