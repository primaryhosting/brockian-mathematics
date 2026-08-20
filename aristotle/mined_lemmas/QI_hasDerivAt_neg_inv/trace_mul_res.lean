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


theorem trace_mul_res (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) (A : Mat n) :
    (A * res ω t).trace = ∑ i, (cj hω A) i i * (((eigV hω i + t)⁻¹ : ℝ) : ℂ) := by
  rw [← trace_cj hω (A * res ω t), cj_mul, cj_res hω ht, trace_mul_diagonal]

