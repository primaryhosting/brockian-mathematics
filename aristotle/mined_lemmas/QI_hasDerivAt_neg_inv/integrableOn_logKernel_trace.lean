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


theorem integrableOn_logKernel_trace (hω : ω.PosDef) (A : Mat n) :
    IntegrableOn (fun t : ℝ => A.trace.re * (1 + t)⁻¹ - (A * res ω t).trace.re) (Ioi 0) := by
  have heq : ∀ t ∈ Ioi (0:ℝ), A.trace.re * (1 + t)⁻¹ - (A * res ω t).trace.re
      = ∑ i, ((cj hω A) i i).re * ((1 + t)⁻¹ - (eigV hω i + t)⁻¹) := by
    intro t ht
    have h1 : A.trace.re = ∑ i, ((cj hω A) i i).re := by
      rw [← trace_cj hω A, Matrix.trace, Complex.re_sum]
      rfl
    have h2 : (A * res ω t).trace.re = ∑ i, ((cj hω A) i i).re * (eigV hω i + t)⁻¹ := by
      rw [trace_mul_res hω (le_of_lt ht), Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [h1, h2, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine MeasureTheory.IntegrableOn.congr_fun ?_ (fun t ht => (heq t ht).symm) measurableSet_Ioi
  exact MeasureTheory.integrable_finset_sum _
    (fun i _ => (integrableOn_logKernel (eigV_pos hω i)).const_mul _)

/-- Integral representation of `Tr (A log ω)`. -/
