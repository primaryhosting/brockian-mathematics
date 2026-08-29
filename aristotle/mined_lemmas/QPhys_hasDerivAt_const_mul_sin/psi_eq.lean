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

lemma psi_eq (L : ℝ) (n : ℕ) :
    psi L n = fun x => Real.sqrt (2 / L) * Real.sin ((n * Real.pi / L) * x) := by
  funext x
  unfold psi
  rw [show (n : ℝ) * Real.pi * x / L = (n * Real.pi / L) * x by ring]

/-- First derivative of `ψ_n`. -/
