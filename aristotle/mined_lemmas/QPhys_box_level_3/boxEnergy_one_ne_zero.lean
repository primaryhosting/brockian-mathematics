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

theorem boxEnergy_one_ne_zero (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 1 ≠ 0 := by
  unfold boxEnergy
  simp [hhbar, hm, hL, Real.pi_ne_zero]

/-- The ratio of the `n`-th to the ground-state energy of the infinite square
well is `n²`, for any nonzero values of `ħ`, `m` and `L`. -/
