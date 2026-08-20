import Mathlib

/-!
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The partial derivative of a Lagrangian `L : ℝ × ℝ → ℝ` with respect to its first
(position) argument, at the point `z = (q, v)`. -/

noncomputable def dL_dq (L : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := fderiv ℝ L z (1, 0)

/-- The partial derivative of a Lagrangian `L : ℝ × ℝ → ℝ` with respect to its second
(velocity) argument, at the point `z = (q, v)`; the *canonical momentum*. -/
