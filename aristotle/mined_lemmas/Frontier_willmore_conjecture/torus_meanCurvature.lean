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

lemma torus_meanCurvature (hr : 0 < r) (hR : r < R) (u v : ℝ) :
    (torusOfRevolution R r).meanCurvature u v
      = (R + 2 * r * cos u) / (2 * r * (R + r * cos u)) := by
  have hw : 0 < R + r * cos u := by nlinarith [Real.neg_one_le_cos u, Real.cos_le_one u]
  simp only [ParamSurface.meanCurvature, torus_Efst, torus_Ffst, torus_Gfst,
    torus_Lsnd hr hR, torus_Msnd hr hR, torus_Nsnd hr hR]
  rw [show r ^ 2 * (R + r * cos u) ^ 2 - (0:ℝ) ^ 2 = (r * (R + r * cos u)) ^ 2 by ring]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

