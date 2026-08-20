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

private lemma exp_half_mul_rpow_neg_half (t : ℝ) :
    Real.exp (t / 2) * (Real.exp t) ^ (-(1 : ℝ) / 2) = 1 := by
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, ← Real.exp_add]
  have : t / 2 + t * (-(1 : ℝ) / 2) = 0 := by ring
  rw [this, Real.exp_zero]

/-- Scalar cancellation: `x^{-1/2} · e^{(log x)/2} = 1` for `0 < x`. -/
