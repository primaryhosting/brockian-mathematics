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

theorem hasDerivAt_neg_inv {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => -(c + t)⁻¹) ((c + t)⁻¹ * (c + t)⁻¹) t := by
  have h0 : c + t ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => c + t) 1 t := by simpa using (hasDerivAt_id t).const_add c
  have h2 := (h1.inv h0).neg
  convert h2 using 1
  field_simp
