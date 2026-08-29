import Mathlib
-- (Lean requires `import` to precede any module documentation, so the required
-- header comment appears immediately below the import.)
/-!
# Box Level 6
Category: Quantum Physics
Target: QPhys.box_level_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well ("particle in a box") of width `L`, with
reduced Planck constant `hbar`:  `E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_ratio (hbar m L : ℝ) (n : ℕ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  field_simp
  ring

/-- For the infinite square well, the ratio of the sixth energy level to the
ground-state energy is `6² = 36`. -/
