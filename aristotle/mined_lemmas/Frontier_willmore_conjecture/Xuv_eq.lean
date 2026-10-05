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

lemma Xuv_eq (R r u v : ℝ) :
    Xuv R r u v = (r * sin u * sin v, -(r * sin u) * cos v, 0) := by
  have h1 : HasDerivAt (fun t : ℝ => -(r * sin u) * cos t) (r * sin u * sin v) v := by
    simpa [mul_comm] using ((Real.hasDerivAt_cos v).const_mul (-(r * sin u)))
  have h2 : HasDerivAt (fun t : ℝ => -(r * sin u) * sin t) (-(r * sin u) * cos v) v := by
    simpa using ((Real.hasDerivAt_sin v).const_mul (-(r * sin u)))
  have h3 : HasDerivAt (fun _ : ℝ => r * cos u) (0 : ℝ) v := hasDerivAt_const _ _
  have := (h1.prodMk (h2.prodMk h3)).deriv
  rw [Xuv]
  simpa only [Xu_eq] using this

