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

lemma aestronglyMeasurable_ofLog {h : ℝ → E} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (ofLog h) (volume.restrict (Ioi (0 : ℝ))) := by
  have h1 : AEStronglyMeasurable (fun x : ℝ => h (Real.log x))
      (volume.restrict (Ioi (0 : ℝ))) :=
    hh.comp_quasiMeasurePreserving log_quasiMeasurePreserving
  have h2 : Measurable fun x : ℝ => (x ^ (-(1 : ℝ) / 2) : ℝ) := by fun_prop
  exact h2.aestronglyMeasurable.smul h1

/-- The substitution preserves membership in `L²`. -/
