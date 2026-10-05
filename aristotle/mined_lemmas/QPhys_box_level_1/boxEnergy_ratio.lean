/-!
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy levels of a particle in a one-dimensional infinite potential well
("particle in a box").  Writing `E₁` for the ground-state energy
(`E₁ = π² ħ² / (2 m L²)` in physical units, kept here as an abstract nonzero
parameter measured in units where it is rational), the `n`-th level is
`E n = n² · E₁`. -/

theorem boxEnergy_ratio {E1 : Rat} (h : E1 ≠ 0) (n : Nat) :
    boxEnergy E1 n / boxEnergy E1 1 = (n : Rat) ^ 2 := by
  show ((n : Rat) ^ 2 * E1) / boxEnergy E1 1 = (n : Rat) ^ 2
  rw [boxEnergy_one, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel E1 h, Rat.mul_one]

/-- **Box Level 1.** The infinite-well energy ratio `E₁ / E₁ = 1²`.

This is the `n = 1` instance of the level-ratio law `Eₙ / E₁ = n²`; the
hypothesis `E1 ≠ 0` (true for a genuine well of finite width and positive mass)
makes the ratio genuinely equal to `1`, via `Rat.mul_inv_cancel`. -/
