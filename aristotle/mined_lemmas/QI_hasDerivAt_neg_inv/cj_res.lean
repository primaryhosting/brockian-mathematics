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


theorem cj_res (hω : ω.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    cj hω (res ω t) = Matrix.diagonal (fun i => (((eigV hω i + t)⁻¹ : ℝ) : ℂ)) := by
  have hpos : (ω + (t : ℂ) • 1).PosDef := posDef_shift hω ht
  rw [cj, res, conj_inv _ _ (eigU_mem hω) hpos.isUnit]
  rw [show star (eigU hω) * (ω + (t : ℂ) • 1) * eigU hω = cj hω (ω + (t:ℂ) • 1) from rfl,
    cj_shift hω t]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff.2 fun i => ?_).trans Matrix.diagonal_one
  have h0 : (eigV hω i + t) ≠ 0 := ne_of_gt (by linarith [eigV_pos hω i])
  have h1 : ((eigV hω i + t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
  push_cast at h1 ⊢
  field_simp

/-- The trace of a product, entrywise. -/
