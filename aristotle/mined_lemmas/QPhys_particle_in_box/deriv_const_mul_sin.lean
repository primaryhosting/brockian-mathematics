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

lemma deriv_const_mul_sin (c k : ℝ) :
    deriv (fun x : ℝ => c * Real.sin (k * x)) = fun x : ℝ => (c * k) * Real.cos (k * x) := by
  funext x
  simpa using (hasDerivAt_const_mul_sin c k x).deriv

/-- Second derivative of `x ↦ c * sin (k * x)`. -/
