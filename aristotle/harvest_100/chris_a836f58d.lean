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

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite potential well
(“particle in a box”) of width `L`, with reduced Planck constant `hbar`:
`Eₙ = n² π² ħ² / (2 m L²)` for `n ≥ 1`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For the infinite square well, the ratio of the seventh energy level to the ground state
energy is `7² = 49`. -/
theorem box_level_7 (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 7 / boxEnergy hbar m L 1 = (7 : ℝ) ^ 2 := by
  have h1 : boxEnergy hbar m L 1 = Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2) := by
    simp [boxEnergy]
  have h7 : boxEnergy hbar m L 7 = 49 * (Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)) := by
    simp [boxEnergy]
    ring
  have hne : Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2) ≠ 0 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    apply div_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ hpi) (pow_ne_zero _ hhbar)
    · exact mul_ne_zero (mul_ne_zero two_ne_zero hm) (pow_ne_zero _ hL)
  rw [h1, h7, mul_div_assoc, div_self hne]
  norm_num

end QPhys

