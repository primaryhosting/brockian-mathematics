/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the required header
-- appears verbatim above as a block comment and is repeated as a module docstring below.)
import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

The substitution `x = e^t` induces a unitary `U : L²(0,∞) ≃ L²(ℝ)`,
`(U f)(t) = e^{t/2} · f(e^t)`, with inverse `(U⁻¹ h)(x) = x^{-1/2} · h(log x)`.

* `Brockian.DilationGenerator.mellin_log_unitary` — the target: the change of variables identity
  `∫_{(0,∞)} ‖f x‖² dx = ∫_ℝ ‖e^{t/2} • f(e^t)‖² dt`, valid for every `f : ℝ → E`.
* `Brockian.DilationGenerator.mellin_log_unitary_symm` — the same for the inverse substitution.
* `Brockian.DilationGenerator.mellinLogLpEquiv` — the upgrade to the `Lp` API: a linear isometry
  equivalence `L²((0,∞)) ≃ₗᵢ L²(ℝ)` implementing `f ↦ (t ↦ e^{t/2} • f (e^t))`.
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

/-! ### The change of variables `x = exp t` -/

/-- The exponential map sends `ℝ` onto the positive half-line. -/

lemma quasiMeasurePreserving_exp :
    Measure.QuasiMeasurePreserving Real.exp volume (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine ⟨Real.measurable_exp, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_exp hs]
  have key := lintegral_Ioi_eq_lintegral_exp_mul (s.indicator 1)
  rw [lintegral_indicator_one hs, hs0] at key
  have hF : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp t) * s.indicator 1 (Real.exp t)) :=
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul
      ((measurable_const.indicator hs).comp Real.measurable_exp)
  have h0 := (lintegral_eq_zero_iff hF).mp key.symm
  have hae : ∀ᵐ t : ℝ, t ∉ Real.exp ⁻¹' s := by
    filter_upwards [h0] with t ht
    simp only [Pi.zero_apply, mul_eq_zero] at ht
    rcases ht with h | h
    · exact absurd h (by positivity)
    · intro hmem
      rw [Set.indicator_of_mem (show Real.exp t ∈ s from hmem)] at h
      simp at h
  rwa [← MeasureTheory.measure_eq_zero_iff_ae_notMem] at hae

/-- `log` pushes the Lebesgue measure on `(0, ∞)` to a measure absolutely continuous with respect
to the Lebesgue measure on `ℝ`. -/
