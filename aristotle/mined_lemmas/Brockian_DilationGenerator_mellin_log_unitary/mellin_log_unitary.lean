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

theorem mellin_log_unitary (f : ℝ → F) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  rw [integral_Ioi_eq_integral_exp_smul (fun x => ‖f x‖ ^ 2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hexp : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [← Real.exp_nat_mul]; norm_num; ring
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, smul_eq_mul,
    hexp]

/-- Scalar cancellation: `e^{t/2} · (eᵗ)^{-1/2} = 1`. -/
