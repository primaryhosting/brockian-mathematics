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


theorem conj_inv (U A : Mat n) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hA : IsUnit A) :
    star U * A⁻¹ * U = (star U * A * U)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← conj_mul _ _ _ hU, Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hA)]
  simpa using Matrix.mem_unitaryGroup_iff'.mp hU

