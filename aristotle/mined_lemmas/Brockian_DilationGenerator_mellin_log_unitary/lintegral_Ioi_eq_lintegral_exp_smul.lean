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

theorem lintegral_Ioi_eq_lintegral_exp_smul (g : ℝ → ENNReal) :
    ∫⁻ x in Ioi (0 : ℝ), g x = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t) := by
  have himg : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    simp [Set.image_univ, Real.range_exp]
  have h :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
      (s := (univ : Set ℝ)) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Real.exp_injective.injOn) g
  rw [himg, Measure.restrict_univ] at h
  simpa [abs_of_pos (Real.exp_pos _)] using h

/-- The substitution `x = exp t` as an identity of Bochner integrals: for any function
`g : ℝ → E`, the integral of `g` over `(0, ∞)` equals the integral of `t ↦ exp t • g (exp t)`
over `ℝ`.  No integrability hypotheses are needed: if one side fails to be integrable, so does
the other, and both integrals are then `0`. -/
