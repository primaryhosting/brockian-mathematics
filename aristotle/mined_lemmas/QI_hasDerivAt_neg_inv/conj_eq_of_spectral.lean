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


theorem conj_eq_of_spectral (U A D : Mat n) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (h : A = U * D * star U) : star U * A * U = D := by
  subst h
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc star U * (U * D * star U) * U = (star U * U) * D * (star U * U) := by noncomm_ring
    _ = D := by rw [h1]; simp

