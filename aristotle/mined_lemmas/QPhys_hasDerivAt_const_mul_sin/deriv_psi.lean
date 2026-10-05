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

open scoped Real

namespace QPhys

/-- The normalized stationary states of the infinite square well of width `L`:
`ψ_n(x) = √(2/L) · sin(nπx/L)`. -/

lemma deriv_psi (L : ℝ) (n : ℕ) :
    deriv (psi L n) =
      fun x => Real.sqrt (2 / L) * (n * Real.pi / L) * Real.cos ((n * Real.pi / L) * x) := by
  funext x
  rw [psi_eq]
  exact (hasDerivAt_const_mul_sin _ _ x).deriv

/-- Second derivative of `ψ_n`: it is `-k²ψ_n` with `k = nπ/L`. -/
