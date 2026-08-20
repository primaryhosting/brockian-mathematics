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


theorem trace_sum_smul_mul (B : Mat n) (c : Y → ℝ) (F : Y → Mat n) :
    ((∑ y, ((c y : ℝ) : ℂ) • F y) * B).trace.re = ∑ y, c y * (F y * B).trace.re := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_assoc, Matrix.trace_smul]
  simp

/-- **Measurement bound**: for any POVM, the measured `χ²`-type quantity is dominated by the
BKM quadratic form. -/
