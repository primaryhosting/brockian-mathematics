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
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The ground-state energy of the infinite well is positive
(for positive mass, width and `ħ`). -/
theorem boxEnergy_one_pos {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hbar_pos : 0 < hbar) : 0 < boxEnergy m L hbar 1 := by
  unfold boxEnergy
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

/-- **Infinite square well, level 2.**  The ratio of the first excited state
energy to the ground state energy is `2² = 4`. -/
theorem box_level_2 {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hbar_pos : 0 < hbar) :
    boxEnergy m L hbar 2 / boxEnergy m L hbar 1 = (2 : ℝ) ^ 2 := by
  have h1 : boxEnergy m L hbar 1 ≠ 0 :=
    ne_of_gt (boxEnergy_one_pos hm hL hbar_pos)
  rw [div_eq_iff h1]
  unfold boxEnergy
  norm_num
  ring

end QPhys

