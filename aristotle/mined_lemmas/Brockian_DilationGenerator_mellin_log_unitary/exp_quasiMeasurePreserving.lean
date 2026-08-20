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

lemma exp_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving Real.exp volume (volume.restrict (Ioi (0 : ℝ))) := by
  refine ⟨Real.measurable_exp, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_exp hs]
  have h := lintegral_Ioi_comp_exp (s.indicator 1)
  rw [lintegral_indicator_one hs, hs0] at h
  have hmeas : Measurable
      (fun t : ℝ => ENNReal.ofReal (Real.exp t) * s.indicator 1 (Real.exp t)) :=
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul
      ((measurable_one.indicator hs).comp Real.measurable_exp)
  have h0 := (lintegral_eq_zero_iff hmeas).1 h.symm
  have key : (Real.exp ⁻¹' s).indicator (1 : ℝ → ℝ≥0∞) =ᵐ[volume] 0 := by
    filter_upwards [h0] with t ht
    simp only [Pi.zero_apply, mul_eq_zero] at ht ⊢
    rcases ht with h1 | h2
    · exact absurd h1 (by simp [Real.exp_pos t])
    · simpa [Set.indicator_apply] using h2
  rw [← lintegral_indicator_one (Real.measurable_exp hs)]
  exact (lintegral_congr_ae key).trans (by simp)

/-- `log` is quasi measure preserving from Lebesgue measure on `(0, ∞)` to Lebesgue measure
on `ℝ`. -/
