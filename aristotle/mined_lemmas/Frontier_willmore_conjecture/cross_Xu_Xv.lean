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

lemma cross_Xu_Xv (R r u v : ℝ) :
    cross3 (Xu R r u v) (Xv R r u v) =
      (-(r * (R + r * cos u) * (cos u * cos v)), -(r * (R + r * cos u) * (cos u * sin v)),
        -(r * (R + r * cos u) * sin u)) := by
  have hv := sin_sq_add_cos_sq v
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [cross3, Xu_eq, Xv_eq]; ring
  · simp only [cross3, Xu_eq, Xv_eq]; ring
  · simp only [cross3, Xu_eq, Xv_eq]
    linear_combination (-(r * sin u * (R + r * cos u))) * hv

