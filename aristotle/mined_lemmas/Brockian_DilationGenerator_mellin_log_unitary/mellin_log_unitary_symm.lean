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

theorem mellin_log_unitary_symm (h : ℝ → F) :
    ∫ t : ℝ, ‖h t‖ ^ 2
      = ∫ x in Ioi (0 : ℝ), ‖(x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x)‖ ^ 2 := by
  rw [mellin_log_unitary (fun x => (x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.log_exp, smul_smul, exp_half_mul_rpow_neg_half t, one_smul]

/-- The two substitutions are mutually inverse: `U⁻¹ (U f) = f` on `(0, ∞)`. -/
