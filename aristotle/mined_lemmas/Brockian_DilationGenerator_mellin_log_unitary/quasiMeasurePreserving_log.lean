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

theorem quasiMeasurePreserving_log :
    Measure.QuasiMeasurePreserving Real.log (volume.restrict (Ioi (0 : ℝ))) volume := by
  refine ⟨Real.measurable_log, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_log hs, Measure.restrict_apply (Real.measurable_log hs)]
  have himg : Real.log ⁻¹' s ∩ Ioi 0 = Real.exp '' s := by
    ext x
    refine ⟨fun hx => ⟨Real.log x, hx.1, Real.exp_log hx.2⟩, ?_⟩
    rintro ⟨t, ht, rfl⟩
    exact ⟨by simpa only [Set.mem_preimage, Real.log_exp] using ht, Real.exp_pos t⟩
  rw [himg]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    (s := s) hs (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn.mono (subset_univ s)) (fun _ => 1)
  simp only [mul_one] at h
  rw [← setLIntegral_one, h, setLIntegral_measure_zero _ _ hs0]

/-- `U` preserves the `L²` norm, as an `eLpNorm` identity, with no hypothesis on `f`. -/
