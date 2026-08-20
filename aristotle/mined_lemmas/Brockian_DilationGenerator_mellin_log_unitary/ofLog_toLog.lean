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
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Real
open scoped ENNReal NNReal

namespace Brockian.DilationGenerator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The substitution `x = exp t` maps `ℝ` onto `(0, ∞)`. -/

lemma ofLog_toLog (f : ℝ → E) {x : ℝ} (hx : 0 < x) : ofLog (toLog f) x = f x := by
  have hlog : Real.exp (Real.log x) = x := Real.exp_log hx
  rw [ofLog_apply, toLog_apply, hlog, smul_smul]
  have hkey : (x ^ (-(1 : ℝ) / 2) : ℝ) * Real.exp (Real.log x / 2) = 1 := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
    rw [show Real.log x * (-(1 : ℝ) / 2) + Real.log x / 2 = 0 by ring, Real.exp_zero]
  rw [hkey, one_smul]

/-- `ofLog` is a right inverse of `toLog`. -/
