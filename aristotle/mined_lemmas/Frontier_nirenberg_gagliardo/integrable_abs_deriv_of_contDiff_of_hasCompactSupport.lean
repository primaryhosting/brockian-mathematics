/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

set_option grind.warning false

namespace Frontier

open MeasureTheory intervalIntegral Set

/-- Auxiliary: for a `C¹` function with compact support on `ℝ`, `|f'|` is integrable. -/

theorem integrable_abs_deriv_of_contDiff_of_hasCompactSupport
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f) :
    Integrable (fun t => |deriv f t|) volume := by
  have hcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hcs : HasCompactSupport (deriv f) := hsupp.deriv
  have : Integrable (deriv f) volume := hcont.integrable_of_hasCompactSupport hcs
  exact this.abs

/-- The one-dimensional endpoint case of the Gagliardo–Nirenberg interpolation
inequality: for a continuously differentiable function `f : ℝ → ℝ` with compact
support, the sup-norm of `f` is bounded by half the `L¹` norm of its derivative,
`‖f‖_∞ ≤ (1/2) ‖f'‖_1`. -/
