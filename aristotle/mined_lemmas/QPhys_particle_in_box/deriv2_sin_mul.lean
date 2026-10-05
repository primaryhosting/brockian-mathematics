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

/-- The `n`-th stationary state of the infinite square well of width `L`:
`ψ_n(x) = sin (n π x / L)` (unnormalized). -/

lemma deriv2_sin_mul :
    deriv (deriv fun y : ℝ => Real.sin (c * y)) = fun x => -(c ^ 2) * Real.sin (c * x) := by
  rw [deriv_sin_mul]
  funext x
  exact (hasDerivAt_cos_mul c x).deriv

end Derivatives

