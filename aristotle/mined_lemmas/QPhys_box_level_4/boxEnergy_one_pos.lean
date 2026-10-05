/-
# Box Level 4
Category: Quantum Physics
Target: QPhys.box_level_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a one-dimensional
infinite potential well ("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_one_pos {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L) (hbar_pos : 0 < hbar) :
    0 < boxEnergy m L hbar 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold boxEnergy
  positivity

/-- **Infinite square well energy ratio.**  For a particle of mass `m > 0` in a box of width
`L > 0` with `ħ > 0`, the fourth level has energy `4² = 16` times the ground-state energy. -/
