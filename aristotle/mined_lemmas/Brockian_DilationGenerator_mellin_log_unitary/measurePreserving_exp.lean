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

lemma measurePreserving_exp :
    MeasurePreserving Real.exp (volume.withDensity expDensity)
      (volume.restrict (Ioi (0 : ℝ))) := by
  refine ⟨Real.measurable_exp, ?_⟩
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply Real.measurable_exp hA, Measure.restrict_apply hA,
    withDensity_apply _ (hA.preimage Real.measurable_exp)]
  have himg : Real.exp '' (Real.exp ⁻¹' A) = A ∩ Ioi (0 : ℝ) := by
    rw [Set.image_preimage_eq_inter_range, Real.range_exp]
  rw [← himg, volume_image_exp (hA.preimage Real.measurable_exp)]

/-- `log` sends Lebesgue measure on `(0, ∞)` to the measure `e^t dt` on `ℝ`. -/
