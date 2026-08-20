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

/-- The `n`-th stationary state of a particle in an infinite square well of width `L`,
`ψ_n(x) = √(2/L) · sin(nπx/L)`. -/

theorem hasDerivAt_boxState (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (boxState L n)
      (Real.sqrt (2 / L) * ((n * Real.pi / L) * Real.cos (n * Real.pi * x / L))) x := by
  unfold boxState
  have hlin : HasDerivAt (fun y : ℝ => (n : ℝ) * Real.pi * y / L) ((n : ℝ) * Real.pi / L) x := by
    simpa [mul_comm, mul_div_assoc] using
      (((hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi)).div_const L)
  have h := (Real.hasDerivAt_sin ((n : ℝ) * Real.pi * x / L)).comp x hlin
  simpa [mul_comm, mul_left_comm, mul_assoc] using h.const_mul (Real.sqrt (2 / L))

/-- The second derivative of the box eigenstate. -/
