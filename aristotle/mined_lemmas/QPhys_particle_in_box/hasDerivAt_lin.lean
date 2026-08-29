import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`Eₙ = n²π²ℏ²/(2mL²)`. -/

lemma hasDerivAt_lin (k x : ℝ) : HasDerivAt (fun y : ℝ => k * y) k x := by
  simpa using (hasDerivAt_id x).const_mul k

/-- A function with everywhere-vanishing derivative is constant. -/
