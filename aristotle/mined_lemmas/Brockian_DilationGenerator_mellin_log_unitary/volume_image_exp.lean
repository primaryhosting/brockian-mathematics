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

lemma volume_image_exp {s : Set ℝ} (hs : MeasurableSet s) :
    volume (Real.exp '' s) = ∫⁻ t in s, expDensity t := by
  have h :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
      hs (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) (Real.exp_injective.injOn)
      (fun _ => 1)
  simpa [expDensity, abs_of_pos (Real.exp_pos _), MeasureTheory.lintegral_one,
    Measure.restrict_apply_univ] using h

