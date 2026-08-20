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

noncomputable def noetherCurrent (L : ℝ × ℝ → ℝ) (X q v : ℝ → ℝ) (t : ℝ) : ℝ :=
  dL_dv L (q t, v t) * X (q t)

/-- **Key intermediate lemma**: along a solution of the Euler–Lagrange equation, the Noether
current attached to an infinitesimal symmetry has vanishing time derivative. -/
