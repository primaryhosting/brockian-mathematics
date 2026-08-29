/-
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite potential well ("particle in a box") of width `L`,
with reduced Planck constant `hbar`:
`Eₙ = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_ratio (m L hbar : ℝ) (hm : m ≠ 0) (hL : L ≠ 0) (hbar0 : hbar ≠ 0) (n : ℕ) :
    boxEnergy m L hbar n / boxEnergy m L hbar 1 = (n : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  push_cast
  field_simp

/-- The infinite-well energy ratio `E₅ / E₁ = 5²`. -/
