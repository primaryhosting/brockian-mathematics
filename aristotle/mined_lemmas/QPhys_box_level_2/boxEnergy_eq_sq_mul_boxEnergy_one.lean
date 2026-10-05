import Mathlib
/-!
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module docstrings, so the single `import Mathlib` line above must come first.

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck
constant `hbar`:  `E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_eq_sq_mul_boxEnergy_one (m L hbar : ℝ) (n : ℕ) :
    boxEnergy m L hbar n = (n : ℝ) ^ 2 * boxEnergy m L hbar 1 := by
  unfold boxEnergy
  norm_num
  ring

/-- For the infinite square well, the ratio of the second energy level to the
ground state energy is `2² = 4`, provided the ground state energy is nonzero
(equivalently, the mass, the well width and `ħ` are all nonzero). -/
