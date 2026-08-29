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

lemma two_mul_r_sqrt_le {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    2 * r * Real.sqrt (R ^ 2 - r ^ 2) ≤ R ^ 2 := by
  have hR0 : 0 < R := lt_trans hr hR
  have hsq : (0:ℝ) ≤ R ^ 2 - r ^ 2 := by nlinarith
  have hs2 := Real.sq_sqrt hsq
  have hnn := Real.sqrt_nonneg (R ^ 2 - r ^ 2)
  nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), sq_nonneg (2 * r * Real.sqrt (R ^ 2 - r ^ 2) - R ^ 2),
    mul_pos hr hR0]

/-- **Willmore's bound for tori of revolution**: the Willmore energy of any torus of
revolution is at least `2π²`. -/
