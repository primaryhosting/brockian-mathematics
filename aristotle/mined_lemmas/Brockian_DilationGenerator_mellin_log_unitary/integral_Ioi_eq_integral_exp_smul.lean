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

theorem integral_Ioi_eq_integral_exp_smul (g : ℝ → F) :
    ∫ x in Ioi (0 : ℝ), g x = ∫ t : ℝ, Real.exp t • g (Real.exp t) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
    (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _)] using h

/-- **The substitution `x = eᵗ` is `L²`-norm preserving.**

The map `f ↦ (fun t => e^{t/2} • f (eᵗ))` sends a function on `(0, ∞)` to a function on `ℝ`
with the same `L²` integral:
`∫_{(0,∞)} ‖f x‖² dx = ∫_ℝ ‖e^{t/2} • f (eᵗ)‖² dt`.
This is the integral identity underlying the unitary `U : L²(0, ∞) ≃ L²(ℝ)` of the Mellin
(logarithmic) change of variables. No hypotheses on `f` are required. -/
