import Mathlib

/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Real-valued companion to `RequestProject/Main.lean`: the infinite square well
spectrum with the explicit physical constants `ħ`, `m`, `L` and `Real.pi`.
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well of width `L`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The spectrum is `n²` times the ground-state energy. -/
theorem boxEnergyReal_eq_sq_mul (hbar m L : ℝ) (n : ℕ) :
    boxEnergyReal hbar m L n = (n : ℝ) ^ 2 * boxEnergyReal hbar m L 1 := by
  unfold boxEnergyReal
  push_cast
  ring

/-- **Infinite square well, level 3 (real form).**  With `ħ, m, L ≠ 0`, the
ratio of the third energy level to the ground-state energy is `3² = 9`. -/
theorem box_level_3_real (hbar m L : ℝ) (hbar_ne : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 3 / boxEnergyReal hbar m L 1 = (3 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergyReal
  push_cast
  field_simp

end QPhys

/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear before any
other command, including module doc comments.  Since this file must *begin* with
the header comment above, it is written in dependency-free core Lean 4.  The
companion file `RequestProject/Box.lean` develops the same physics with Mathlib,
using real numbers, `Real.pi`, and the explicit constants `ħ`, `m`, `L`.
-/

namespace QPhys

/-- Stationary-state energies of a particle of mass `m` in a one-dimensional
infinite square well ("particle in a box") of width `L`:

  `E n = n² · π²ħ²/(2mL²) = n² · E₁`,

where `E₁` is the ground-state energy.  Here the spectrum is parameterised by
the ground-state energy `E₁` (the overall energy scale), so that
`boxEnergy E₁ n` is the energy of the `n`-th level. -/
def boxEnergy (E1 : Rat) (n : Nat) : Rat := (n : Rat) ^ 2 * E1

@[simp] theorem boxEnergy_def (E1 : Rat) (n : Nat) :
    boxEnergy E1 n = (n : Rat) ^ 2 * E1 := rfl

/-- The ground state indeed has energy `E₁`. -/
theorem boxEnergy_one (E1 : Rat) : boxEnergy E1 1 = E1 := by
  have h1 : ((1 : Nat) : Rat) ^ 2 = 1 := rfl
  rw [boxEnergy_def, h1, Rat.one_mul]

/-- **Infinite square well, level 3.**  The energy of the third level of a
particle in a box is `3² = 9` times the ground-state energy:
`E₃ / E₁ = 3²`. -/
theorem box_level_3 (E1 : Rat) (h : E1 ≠ 0) :
    boxEnergy E1 3 / boxEnergy E1 1 = (3 : Rat) ^ 2 := by
  have h3 : ((3 : Nat) : Rat) = 3 := rfl
  have h1 : ((1 : Nat) : Rat) ^ 2 = 1 := rfl
  rw [boxEnergy_def, boxEnergy_def, h3, h1, Rat.one_mul, Rat.div_def,
    Rat.mul_assoc, Rat.mul_inv_cancel E1 h, Rat.mul_one]

end QPhys

