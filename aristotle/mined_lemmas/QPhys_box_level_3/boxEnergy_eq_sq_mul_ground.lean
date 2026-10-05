import Mathlib
/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well ("particle in a box") of width `L`,
with reduced Planck constant `ħ`:
`E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_eq_sq_mul_ground (hbar m L : ℝ) (n : ℕ) :
    boxEnergy hbar m L n = (n : ℝ) ^ 2 * boxEnergy hbar m L 1 := by
  unfold boxEnergy
  push_cast
  ring

/-- The ground-state energy is nonzero whenever `ħ`, `m` and `L` are. -/
