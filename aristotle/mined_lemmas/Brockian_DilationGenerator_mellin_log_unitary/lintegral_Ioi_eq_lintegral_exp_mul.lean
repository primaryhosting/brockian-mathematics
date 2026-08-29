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

theorem lintegral_Ioi_eq_lintegral_exp_mul (g : ℝ → ENNReal) :
    ∫⁻ x in Set.Ioi (0 : ℝ), g x
      = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
      (s := Set.univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn g
  rw [image_exp_univ] at h
  simpa [abs_of_pos (Real.exp_pos _), Measure.restrict_univ] using h

/-! ### The Mellin logarithmic substitution and its inverse -/

/-- `(U f)(t) = e^{t/2} • f (e^t)`, the logarithmic substitution on functions. -/
