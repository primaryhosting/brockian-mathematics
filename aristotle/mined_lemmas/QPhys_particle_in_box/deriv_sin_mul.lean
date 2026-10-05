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

lemma deriv_sin_mul :
    deriv (fun y : ℝ => Real.sin (c * y)) = fun x => c * Real.cos (c * x) := by
  funext x
  exact (hasDerivAt_sin_mul c x).deriv

