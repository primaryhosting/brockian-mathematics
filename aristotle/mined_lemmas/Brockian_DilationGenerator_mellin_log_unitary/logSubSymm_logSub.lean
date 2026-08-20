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

theorem logSubSymm_logSub (f : ℝ → F) {x : ℝ} (hx : 0 < x) : logSubSymm (logSub f) x = f x := by
  simp only [logSub, logSubSymm, smul_smul, Real.exp_log hx, rpow_neg_half_mul_exp_half hx,
    one_smul]

/-- The two substitutions are mutually inverse: `U (U⁻¹ h) = h` on `ℝ`. -/
