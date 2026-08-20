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


theorem trace_omega_sq (hω : ω.PosDef) {A : Mat n} (hA : A.IsHermitian) :
    (ω * A * A).trace = ((∑ i, ∑ j, eigV hω i * ‖cj hω A i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [← trace_cj hω (ω * A * A), cj_mul, cj_mul, cj_self hω, trace_mul_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : cj hω A j i = (starRingEnd ℂ) (cj hω A i j) :=
    ((cj_isHermitian hω hA).apply j i).symm
  simp only [Matrix.diagonal_mul]
  rw [h1]
  linear_combination (eigV hω i : ℂ) * mul_conj_norm (cj hω A i j)

/-- **Key inequality**: the BKM quadratic form dominates `2 Tr(Δ A) - Tr(ω A²)` for every
Hermitian `A`.  This is the operator form of the fact that the logarithmic mean is at most the
arithmetic mean. -/
