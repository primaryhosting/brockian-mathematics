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

@[simp] theorem boxEnergy_one (E1 : Rat) : boxEnergy E1 1 = E1 := by
  show ((1 : Rat) ^ 2) * E1 = E1
  rw [show ((1 : Rat) ^ 2) = 1 from rfl, Rat.one_mul]

/-- The ground-state energy is nonzero, so ratios against it are well defined. -/
