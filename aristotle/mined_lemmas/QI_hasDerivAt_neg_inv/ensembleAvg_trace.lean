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


theorem ensembleAvg_trace (hp1 : ∑ x, p x = 1) (hρ : ∀ x, (ρ x).trace = 1) :
    (ensembleAvg p ρ).trace = 1 := by
  rw [ensembleAvg, Matrix.trace_sum]
  simp only [Matrix.trace_smul, hρ, smul_eq_mul, mul_one]
  rw [← Complex.ofReal_sum, hp1, Complex.ofReal_one]

/-- The Holevo quantity is the average relative entropy of the members of the ensemble to its
average state. -/
