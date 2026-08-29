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

noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * (Real.pi ^ 2 * hbar ^ 2) / (2 * m * L ^ 2)

/-- The ground-state energy of the infinite well is nonzero when `ħ`, `m`, `L`
are nonzero. -/
