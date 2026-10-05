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

theorem boxEnergy_ratio (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) (n : ℕ) :
    boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  rw [boxEnergy_eq_sq_mul_ground hbar m L n, mul_div_assoc,
    div_self (boxEnergy_one_ne_zero hbar m L hhbar hm hL), mul_one]

/-- **Infinite square well, level 3.** The ratio of the third energy level to
the ground-state energy of a particle in a one-dimensional infinite well is
`3² = 9`, independently of the mass, the well width and `ħ`. -/
