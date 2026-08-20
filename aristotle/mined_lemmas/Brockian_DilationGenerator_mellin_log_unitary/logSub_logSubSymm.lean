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

theorem logSub_logSubSymm (h : ℝ → F) : logSub (logSubSymm h) = h := by
  funext t
  simp only [logSub, logSubSymm, Real.log_exp, smul_smul, exp_half_mul_rpow_neg_half t, one_smul]

/-! ## Upgrade to a unitary equivalence `L²(0,∞) ≃ L²(ℝ)` -/

/-- Change of variables `x = eᵗ` for lower Lebesgue integrals. -/
