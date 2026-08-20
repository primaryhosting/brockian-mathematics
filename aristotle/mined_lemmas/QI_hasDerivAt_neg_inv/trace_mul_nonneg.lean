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


theorem trace_mul_nonneg (hω : ω.PosDef) {F : Mat n} (hF : F.PosSemidef) :
    0 ≤ (ω * F).trace.re := by
  rw [trace_mul_re_eq_sum_eig hω]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (eigV_pos hω i).le (diag_re_nonneg (cj_posSemidef hω hF) i)

/-- If `ω` is positive definite, `F` is positive semidefinite and `Tr (ω F) = 0`, then `F = 0`. -/
