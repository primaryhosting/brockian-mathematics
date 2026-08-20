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

lemma deriv2_const_mul_sin (c k : ℝ) :
    deriv (deriv (fun x : ℝ => c * Real.sin (k * x)))
      = fun x : ℝ => -(c * k ^ 2) * Real.sin (k * x) := by
  rw [deriv_const_mul_sin]
  funext x
  have h : HasDerivAt (fun x : ℝ => k * x) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have := (h.cos).const_mul (c * k)
  have hd := this.deriv
  rw [hd]
  ring

/-- The eigenstates are normalized: `∫₀^L |ψ n|² = 1` for a well of positive width `L`. -/
