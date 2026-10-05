import Mathlib
/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real

namespace QPhys

/-- The (unnormalized) stationary state of a particle in an infinite square well
of width `L`: `ψₙ(x) = sin (n π x / L)`. -/

lemma hasDerivAt_cos_mul (k x : ℝ) :
    HasDerivAt (fun y : ℝ => k * Real.cos (k * y)) (-(k ^ 2 * Real.sin (k * x))) x := by
  have h : HasDerivAt (fun y : ℝ => k * y) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have := ((Real.hasDerivAt_cos (k * x)).comp x h).const_mul k
  convert this using 1
  ring

