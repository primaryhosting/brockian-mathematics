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

lemma norm_sq_mellinLogMap (f : ℝ → E) (t : ℝ) :
    ‖mellinLogMap f t‖ ^ 2 = Real.exp t * ‖f (Real.exp t)‖ ^ 2 := by
  simp only [mellinLogMap, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    exp_half_sq]

/-- `U⁻¹ ∘ U = id` on the positive half line. -/
