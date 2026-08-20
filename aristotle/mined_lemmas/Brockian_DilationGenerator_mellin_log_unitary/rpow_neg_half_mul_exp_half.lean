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

private lemma rpow_neg_half_mul_exp_half {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 : ℝ) / 2) * Real.exp (Real.log x / 2) = 1 := by
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  have : Real.log x * (-(1 : ℝ) / 2) + Real.log x / 2 = 0 := by ring
  rw [this, Real.exp_zero]

/-- The inverse substitution `t = log x` is also `L²`-norm preserving:
`∫_ℝ ‖h t‖² dt = ∫_{(0,∞)} ‖x^{-1/2} • h (log x)‖² dx`. -/
