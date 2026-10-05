/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Real

/-! ## Partial derivatives of functions of two real variables -/

/-- Partial derivative with respect to the first variable. -/

lemma torus_Nsnd (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    (torusOfRevolution R r).Nsnd u v = (R + r * cos u) * cos u := by
  have hw : 0 < R + r * cos u := by nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]
  simp only [ParamSurface.Nsnd, pd2_pd2_torus_x, pd2_pd2_torus_y, pd2_pd2_torus_z,
    torus_nrm1, torus_nrm2, torus_nrm3, torus_nrmLen hr hR]
  rw [div_eq_iff (by positivity)]
  linear_combination (r * cos u * (R + r * cos u) ^ 2) * Real.sin_sq_add_cos_sq v

