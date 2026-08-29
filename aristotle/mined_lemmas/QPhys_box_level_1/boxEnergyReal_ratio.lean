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

theorem boxEnergyReal_ratio {hbar m L : ℝ} (hh : hbar ≠ 0) (hm : m ≠ 0)
    (hL : L ≠ 0) (n : ℕ) :
    boxEnergyReal hbar m L n / boxEnergyReal hbar m L 1 = (n : ℝ) ^ 2 := by
  have h1 : boxEnergyReal hbar m L 1 ≠ 0 := boxEnergyReal_one_ne_zero hh hm hL
  have hden : (2 * m * L ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hm) (pow_ne_zero _ hL)
  have hnum : (Real.pi ^ 2 * hbar ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero) (pow_ne_zero _ hh)
  simp only [boxEnergyReal, Nat.cast_one, one_pow, one_mul] at h1 ⊢
  field_simp

/-- **Box Level 1** over the reals: `E₁ / E₁ = 1²`. -/
