import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
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

namespace QPhys

/-- The `n`-th (unnormalized) stationary state of a particle in an infinite square
well of width `L`: `ψₙ(x) = sin (n π x / L)`. -/

lemma hasDerivAt_cos_lin :
    HasDerivAt (fun y : ℝ => Real.cos (c * y)) (-(c * Real.sin (c * x))) x := by
  have h := (Real.hasDerivAt_cos (c * x)).comp x
    (by simpa using (hasDerivAt_id x).const_mul c)
  simpa [mul_comm] using h

