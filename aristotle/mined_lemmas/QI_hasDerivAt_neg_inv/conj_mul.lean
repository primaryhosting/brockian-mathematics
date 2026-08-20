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


theorem conj_mul (U A B : Mat n) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    star U * (A * B) * U = (star U * A * U) * (star U * B * U) := by
  calc star U * (A * B) * U = star U * A * (U * star U) * B * U := by
        rw [show U * star U = 1 from Matrix.mem_unitaryGroup_iff.mp hU]; noncomm_ring
    _ = (star U * A * U) * (star U * B * U) := by noncomm_ring

