/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Set Real

namespace Brockian
namespace DilationGenerator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The substitution operator `U : (U f)(t) = e^{t/2} · f(eᵗ)`, at the level of functions. -/

theorem quasiMeasurePreserving_exp :
    Measure.QuasiMeasurePreserving Real.exp volume (volume.restrict (Ioi (0 : ℝ))) := by
  refine ⟨Real.measurable_exp, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_exp hs]
  have h1 : ∫⁻ x in Ioi (0 : ℝ), s.indicator 1 x = 0 := by
    rw [lintegral_indicator_one hs]; simpa using hs0
  rw [lintegral_Ioi_eq_lintegral_exp_mul] at h1
  have hmeas : Measurable fun t : ℝ =>
      ENNReal.ofReal (Real.exp t) * s.indicator (1 : ℝ → ENNReal) (Real.exp t) :=
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul
      ((measurable_one.indicator hs).comp Real.measurable_exp)
  have h2 := (lintegral_eq_zero_iff hmeas).mp h1
  refine measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [h2] with t ht hts
  have hts' : Real.exp t ∈ s := hts
  rw [Pi.zero_apply, Set.indicator_of_mem hts', Pi.one_apply, mul_one] at ht
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos t)).ne' ht

/-- `log` pulls back null sets of `volume` to null sets of `volume.restrict (Ioi 0)`. -/
