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

lemma log_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving Real.log (volume.restrict (Ioi (0 : ℝ))) volume := by
  refine ⟨Real.measurable_log, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_log hs, ← lintegral_indicator_one (Real.measurable_log hs),
    lintegral_Ioi_comp_exp]
  have key : ∀ᵐ t : ℝ,
      ENNReal.ofReal (Real.exp t) * (Real.log ⁻¹' s).indicator 1 (Real.exp t) = 0 := by
    have hs' : s.indicator (1 : ℝ → ℝ≥0∞) =ᵐ[volume] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      simp only [Pi.zero_apply, Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero,
        imp_false, not_not]
      simpa using hs0
    filter_upwards [hs'] with t ht
    by_cases h : t ∈ s
    · simp [h] at ht
    · simp [h]
  rw [lintegral_congr_ae key]
  simp

