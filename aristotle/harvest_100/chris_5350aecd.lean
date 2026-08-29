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
def boxEnergy (E1 : Rat) (n : Nat) : Rat := (n : Rat) ^ 2 * E1

@[simp] theorem boxEnergy_one (E1 : Rat) : boxEnergy E1 1 = E1 := by
  show ((1 : Rat) ^ 2) * E1 = E1
  rw [show ((1 : Rat) ^ 2) = 1 from rfl, Rat.one_mul]

/-- The ground-state energy is nonzero, so ratios against it are well defined. -/
theorem boxEnergy_one_ne_zero {E1 : Rat} (h : E1 ≠ 0) : boxEnergy E1 1 ≠ 0 := by
  rw [boxEnergy_one]; exact h

/-- General level-ratio law for the infinite well: `Eₙ / E₁ = n²`. -/
theorem boxEnergy_ratio {E1 : Rat} (h : E1 ≠ 0) (n : Nat) :
    boxEnergy E1 n / boxEnergy E1 1 = (n : Rat) ^ 2 := by
  show ((n : Rat) ^ 2 * E1) / boxEnergy E1 1 = (n : Rat) ^ 2
  rw [boxEnergy_one, Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel E1 h, Rat.mul_one]

/-- **Box Level 1.** The infinite-well energy ratio `E₁ / E₁ = 1²`.

This is the `n = 1` instance of the level-ratio law `Eₙ / E₁ = n²`; the
hypothesis `E1 ≠ 0` (true for a genuine well of finite width and positive mass)
makes the ratio genuinely equal to `1`, via `Rat.mul_inv_cancel`. -/
theorem box_level_1 {E1 : Rat} (h : E1 ≠ 0) :
    boxEnergy E1 1 / boxEnergy E1 1 = ((1 : Nat) : Rat) ^ 2 := by
  simpa using boxEnergy_ratio h 1

end QPhys

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Box Level 1 — real-valued companion

Mathlib companion to `RequestProject/QPhys.lean`: the same statement, but with
the physical energy levels `E n = n² π² ħ² / (2 m L²)` taken in `ℝ`.
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite potential well of width `L`, with reduced Planck
constant `hbar`:  `E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * (Real.pi ^ 2 * hbar ^ 2) / (2 * m * L ^ 2)

/-- The ground-state energy of the infinite well is nonzero when `ħ`, `m`, `L`
are nonzero. -/
theorem boxEnergyReal_one_ne_zero {hbar m L : ℝ} (hh : hbar ≠ 0) (hm : m ≠ 0)
    (hL : L ≠ 0) : boxEnergyReal hbar m L 1 ≠ 0 := by
  simp only [boxEnergyReal, Nat.cast_one, one_pow, one_mul]
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero) (pow_ne_zero _ hh))
    (mul_ne_zero (mul_ne_zero two_ne_zero hm) (pow_ne_zero _ hL))

/-- General level-ratio law over `ℝ`:  `Eₙ / E₁ = n²`. -/
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
theorem box_level_1_real {hbar m L : ℝ} (hh : hbar ≠ 0) (hm : m ≠ 0)
    (hL : L ≠ 0) :
    boxEnergyReal hbar m L 1 / boxEnergyReal hbar m L 1 = ((1 : ℕ) : ℝ) ^ 2 := by
  simpa using boxEnergyReal_ratio hh hm hL 1

end QPhys

