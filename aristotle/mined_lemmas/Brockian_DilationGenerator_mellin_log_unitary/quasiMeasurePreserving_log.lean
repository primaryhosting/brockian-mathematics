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

lemma quasiMeasurePreserving_log :
    Measure.QuasiMeasurePreserving Real.log (volume.restrict (Set.Ioi (0 : ℝ))) volume := by
  refine ⟨Real.measurable_log, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_log hs]
  have key := lintegral_Ioi_eq_lintegral_exp_mul ((Real.log ⁻¹' s).indicator 1)
  rw [lintegral_indicator_one (hs.preimage Real.measurable_log)] at key
  rw [key]
  have hpt : ∀ t : ℝ, ENNReal.ofReal (Real.exp t) * (Real.log ⁻¹' s).indicator 1 (Real.exp t)
      = s.indicator (fun t => ENNReal.ofReal (Real.exp t)) t := by
    intro t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem (show Real.exp t ∈ Real.log ⁻¹' s by simpa [Real.log_exp] using ht),
        Set.indicator_of_mem ht]
      simp
    · rw [Set.indicator_of_notMem (by simpa [Real.log_exp] using ht),
        Set.indicator_of_notMem ht]
      simp
  simp_rw [hpt]
  rw [lintegral_indicator hs, Measure.restrict_eq_zero.mpr hs0, lintegral_zero_measure]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Almost everywhere equality is preserved by precomposition with `exp`. -/
