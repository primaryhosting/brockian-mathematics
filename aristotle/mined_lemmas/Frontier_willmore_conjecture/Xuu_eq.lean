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

lemma Xuu_eq (R r u v : ℝ) :
    Xuu R r u v = (-(r * cos u) * cos v, -(r * cos u) * sin v, -(r * sin u)) := by
  have h1 : HasDerivAt (fun t : ℝ => -(r * sin t) * cos v) (-(r * cos u) * cos v) u := by
    have : HasDerivAt (fun t : ℝ => -(r * sin t)) (-(r * cos u)) u := by
      simpa using ((Real.hasDerivAt_sin u).const_mul r).neg
    exact this.mul_const _
  have h2 : HasDerivAt (fun t : ℝ => -(r * sin t) * sin v) (-(r * cos u) * sin v) u := by
    have : HasDerivAt (fun t : ℝ => -(r * sin t)) (-(r * cos u)) u := by
      simpa using ((Real.hasDerivAt_sin u).const_mul r).neg
    exact this.mul_const _
  have h3 : HasDerivAt (fun t : ℝ => r * cos t) (-(r * sin u)) u := by
    simpa [mul_comm] using ((Real.hasDerivAt_cos u).const_mul r)
  have := (h1.prodMk (h2.prodMk h3)).deriv
  rw [Xuu]
  simpa only [Xu_eq] using this

