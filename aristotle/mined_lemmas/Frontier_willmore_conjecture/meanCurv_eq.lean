/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- therefore a plain block comment, and is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

open Real intervalIntegral

/-! ## Vector algebra in `ℝ³`

We use `ℝ × ℝ × ℝ` as a model of `ℝ³` together with explicitly defined dot product,
cross product and Euclidean norm.  (The ambient `Prod` norm of Mathlib is the sup norm,
so we never use `‖·‖`; note that the notion of (Fréchet/one-variable) derivative does
not depend on the choice of an equivalent norm, so `deriv` below is the usual derivative
of an `ℝ³`-valued function.) -/

/-- Euclidean dot product on `ℝ³`. -/

lemma meanCurv_eq {R r u v : ℝ} (hr : 0 < r) (hR : r < R) :
    meanCurv R r u v = (R + 2 * r * cos u) / (2 * r * (R + r * cos u)) := by
  have hp := radial_pos (u := u) hr hR
  rw [meanCurv, forme_eq hr hR, formf_eq hr hR, formg_eq hr hR, formE_eq, formF_eq, formG_eq]
  have h1 : 2 * (r ^ 2 * (R + r * cos u) ^ 2 - (0:ℝ) ^ 2) ≠ 0 := by
    have : (0:ℝ) < 2 * (r ^ 2 * (R + r * cos u) ^ 2 - (0:ℝ) ^ 2) := by nlinarith [mul_pos hr hp]
    exact ne_of_gt this
  have h2 : 2 * r * (R + r * cos u) ≠ 0 := by positivity
  rw [div_eq_div_iff h1 h2]
  ring

/-- The classical formula for the area element of a torus of revolution. -/
