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


theorem trace_omega_res_quad_re (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) (Δ : Mat n) :
    (ω * res ω t * Δ * res ω t).trace.re
      = ∑ i, ((cj hω Δ) i i).re * (eigV hω i * ((eigV hω i + t)⁻¹ * (eigV hω i + t)⁻¹)) := by
  rw [trace_res_quad hω ht ω Δ, cj_self hω]
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hre : ((eigV hω i : ℝ) : ℂ) * (((eigV hω i + t)⁻¹ : ℝ) : ℂ) * (cj hω Δ) i i
        * (((eigV hω i + t)⁻¹ : ℝ) : ℂ)
      = ((eigV hω i * ((eigV hω i + t)⁻¹ * (eigV hω i + t)⁻¹) : ℝ) : ℂ) * (cj hω Δ) i i := by
    push_cast
    ring
  rw [hre]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

