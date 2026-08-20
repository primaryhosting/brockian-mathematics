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

lemma aestronglyMeasurable_mellinLog {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (mellinLog f) volume := by
  have h1 : AEStronglyMeasurable (f ∘ Real.exp) (volume.withDensity expDensity) :=
    hf.comp_measurePreserving measurePreserving_exp
  have h2 : AEStronglyMeasurable (f ∘ Real.exp) volume :=
    h1.mono_ac volume_absolutelyContinuous_withDensity_exp
  have h3 : AEStronglyMeasurable (fun t : ℝ => Real.exp (t / 2)) volume :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).aestronglyMeasurable
  exact h3.smul h2

