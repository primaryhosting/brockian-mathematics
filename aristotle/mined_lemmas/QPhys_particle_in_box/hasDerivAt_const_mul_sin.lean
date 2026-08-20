/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Real

/-- First derivative of `x ↦ c * sin (k * x)`. -/

lemma hasDerivAt_const_mul_sin (c k x : ℝ) :
    HasDerivAt (fun x : ℝ => c * Real.sin (k * x)) (c * k * Real.cos (k * x)) x := by
  have h : HasDerivAt (fun x : ℝ => k * x) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have := (h.sin).const_mul c
  convert this using 1
  ring

