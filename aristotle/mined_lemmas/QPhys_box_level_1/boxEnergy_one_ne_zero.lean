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

theorem boxEnergy_one_ne_zero {E1 : Rat} (h : E1 ≠ 0) : boxEnergy E1 1 ≠ 0 := by
  rw [boxEnergy_one]; exact h

/-- General level-ratio law for the infinite well: `Eₙ / E₁ = n²`. -/
