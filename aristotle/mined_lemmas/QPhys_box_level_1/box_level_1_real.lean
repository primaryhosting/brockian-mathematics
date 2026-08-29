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

theorem box_level_1_real {hbar m L : ℝ} (hh : hbar ≠ 0) (hm : m ≠ 0)
    (hL : L ≠ 0) :
    boxEnergyReal hbar m L 1 / boxEnergyReal hbar m L 1 = ((1 : ℕ) : ℝ) ^ 2 := by
  simpa using boxEnergyReal_ratio hh hm hL 1

end QPhys

