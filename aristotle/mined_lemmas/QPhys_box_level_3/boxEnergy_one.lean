import Mathlib

/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Real-valued companion to `RequestProject/Main.lean`: the infinite square well
spectrum with the explicit physical constants `ħ`, `m`, `L` and `Real.pi`.
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well of width `L`:
`E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_one (E1 : Rat) : boxEnergy E1 1 = E1 := by
  have h1 : ((1 : Nat) : Rat) ^ 2 = 1 := rfl
  rw [boxEnergy_def, h1, Rat.one_mul]

/-- **Infinite square well, level 3.**  The energy of the third level of a
particle in a box is `3² = 9` times the ground-state energy:
`E₃ / E₁ = 3²`. -/
