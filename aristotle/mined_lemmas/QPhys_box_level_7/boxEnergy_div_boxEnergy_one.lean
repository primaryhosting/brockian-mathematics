import Mathlib

/-!
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square well
("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_div_boxEnergy_one (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0)
    (n : ℕ) : boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  field_simp
  norm_num

/-- For the one-dimensional infinite square well, the ratio of the seventh energy level
to the ground-state energy is `7² = 49`. -/
