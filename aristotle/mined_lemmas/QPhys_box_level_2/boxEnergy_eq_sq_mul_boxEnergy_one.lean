/-
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite potential well
("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_eq_sq_mul_boxEnergy_one (m L hbar : ℝ) (n : ℕ) :
    boxEnergy m L hbar n = (n : ℝ) ^ 2 * boxEnergy m L hbar 1 := by
  unfold boxEnergy
  push_cast
  ring

/-- The ground state energy is nonzero exactly when the mass, the width and `ħ` are nonzero. -/
