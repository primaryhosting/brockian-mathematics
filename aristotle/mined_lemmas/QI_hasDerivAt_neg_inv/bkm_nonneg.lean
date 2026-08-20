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


theorem bkm_nonneg (hω : ω.PosDef) (hΔ : Δ.IsHermitian) : 0 ≤ bkm ω Δ := by
  rw [bkm_eq_sum hω hΔ]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  refine mul_nonneg (by positivity) ?_
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  simp only [mem_Ioi] at ht
  have h1 : 0 < eigV hω i + t := by linarith [eigV_pos hω i]
  have h2 : 0 < eigV hω j + t := by linarith [eigV_pos hω j]
  positivity

/-- Trace of `Δ * A` in the eigenbasis of `ω`. -/
