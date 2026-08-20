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


theorem trace_res_quad_ofReal (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) (hΔ : Δ.IsHermitian) :
    (Δ * res ω t * Δ * res ω t).trace
      = ((∑ i, ∑ j, ‖cj hω Δ i j‖ ^ 2 * ((eigV hω i + t)⁻¹ * (eigV hω j + t)⁻¹) : ℝ) : ℂ) := by
  rw [trace_res_quad hω ht Δ Δ]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : cj hω Δ j i = (starRingEnd ℂ) (cj hω Δ i j) :=
    ((cj_isHermitian hω hΔ).apply j i).symm
  rw [h1]
  linear_combination ((((eigV hω j : ℂ) + t)⁻¹ * (((eigV hω i : ℂ)) + t)⁻¹)) *
    mul_conj_norm (cj hω Δ i j)

/-- The integrand of the BKM form, in the eigenbasis of `ω`. -/
