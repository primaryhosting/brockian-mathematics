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

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck
constant `hbar`:  `Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The ground-state energy of the infinite well is nonzero whenever the mass,
the width and `ħ` are nonzero. -/
theorem boxEnergy_one_ne_zero {m L hbar : ℝ} (hm : m ≠ 0) (hL : L ≠ 0)
    (hbar0 : hbar ≠ 0) : boxEnergy m L hbar 1 ≠ 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  simp only [Nat.cast_one, one_pow, one_mul]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hpi) (pow_ne_zero 2 hbar0))
    (mul_ne_zero (mul_ne_zero two_ne_zero hm) (pow_ne_zero 2 hL))

/-- **Infinite square well, second level.**  The ratio of the first excited
state energy to the ground state energy is `2² = 4`. -/
theorem box_level_2 {m L hbar : ℝ} (hm : m ≠ 0) (hL : L ≠ 0) (hbar0 : hbar ≠ 0) :
    boxEnergy m L hbar 2 / boxEnergy m L hbar 1 = (2 : ℝ) ^ 2 := by
  have h1 : boxEnergy m L hbar 1 ≠ 0 := boxEnergy_one_ne_zero hm hL hbar0
  rw [div_eq_iff h1]
  unfold boxEnergy
  push_cast
  field_simp

end QPhys

