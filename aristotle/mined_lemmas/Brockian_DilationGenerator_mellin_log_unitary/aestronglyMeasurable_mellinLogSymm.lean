import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The substitution `x = exp t` as an identity of Lebesgue (`ℝ≥0∞`-valued) integrals:
integrating over `(0, ∞)` is the same as integrating `exp t • ·` over all of `ℝ`. -/

lemma aestronglyMeasurable_mellinLogSymm {h : ℝ → E} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (mellinLogSymm h) (volume.restrict (Ioi (0 : ℝ))) := by
  have h1 : AEStronglyMeasurable h (volume.withDensity expDensity) :=
    hh.mono_ac (withDensity_absolutelyContinuous _ _)
  have h2 : AEStronglyMeasurable (h ∘ Real.log) (volume.restrict (Ioi (0 : ℝ))) :=
    h1.comp_measurePreserving measurePreserving_log
  have h3 : AEStronglyMeasurable (fun x : ℝ => x ^ (-(1 : ℝ) / 2))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Measurable.pow_const (f := fun x : ℝ => x) measurable_id _).aestronglyMeasurable
  exact h3.smul h2

