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

theorem boxEnergyReal_eq_sq_mul (hbar m L : ℝ) (n : ℕ) :
    boxEnergyReal hbar m L n = (n : ℝ) ^ 2 * boxEnergyReal hbar m L 1 := by
  unfold boxEnergyReal
  push_cast
  ring

/-- **Infinite square well, level 3 (real form).**  With `ħ, m, L ≠ 0`, the
ratio of the third energy level to the ground-state energy is `3² = 9`. -/
