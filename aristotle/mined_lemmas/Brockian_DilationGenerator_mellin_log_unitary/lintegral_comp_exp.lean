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

open scoped Real ENNReal
open MeasureTheory Set

namespace Brockian
namespace DilationGenerator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The image of `ℝ` under `exp` is the positive half line. -/

theorem lintegral_comp_exp (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioi (0 : ℝ), g x = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [image_exp_univ, Measure.restrict_univ] at h
  simpa only [abs_of_pos (Real.exp_pos _)] using h

/-- The `L²`-Lebesgue integral is preserved by `U`, with no integrability assumption. -/
