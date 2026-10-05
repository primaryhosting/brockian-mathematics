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

open scoped Real ENNReal
open MeasureTheory Set

namespace Brockian
namespace DilationGenerator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The image of `ℝ` under `exp` is the positive half line. -/

lemma mellinLogMapInv_mellinLogMap (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    mellinLogMapInv (mellinLogMap f) x = f x := by
  have hlog : Real.exp (Real.log x) = x := Real.exp_log hx
  simp only [mellinLogMapInv, mellinLogMap, hlog, smul_smul]
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  have : Real.log x * (-(1 : ℝ) / 2) + Real.log x / 2 = 0 := by ring
  rw [this, Real.exp_zero, one_smul]

/-- `U ∘ U⁻¹ = id` on `ℝ`. -/
