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

lemma integral_inv_radial {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    ∫ u in (0:ℝ)..(2 * π), 1 / (R + r * cos u) = 2 * π / Real.sqrt (R ^ 2 - r ^ 2) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 2 * π)
    (f := fun t : ℝ => (t - 2 * arctan (r * sin t / (R + Real.sqrt (R ^ 2 - r ^ 2) + r * cos t)))
          / Real.sqrt (R ^ 2 - r ^ 2))
    (f' := fun u : ℝ => 1 / (R + r * cos u))
    (fun x _ => hasDerivAt_willmoreAntideriv hr hR x)
    ((continuous_inv_radial hr hR).intervalIntegrable _ _)
  rw [h]
  simp

/-- Pointwise, `H² · dA = cos u + (R²/4r) · 1/(R + r cos u)`. -/
