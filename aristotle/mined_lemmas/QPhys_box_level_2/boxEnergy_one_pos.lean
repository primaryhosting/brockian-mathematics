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

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck
constant `hbar`:  `E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_one_pos {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hbar_pos : 0 < hbar) : 0 < boxEnergy m L hbar 1 := by
  unfold boxEnergy
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

/-- **Infinite square well, level 2.**  The ratio of the first excited state
energy to the ground state energy is `2² = 4`. -/
