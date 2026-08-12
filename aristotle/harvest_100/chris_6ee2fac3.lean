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
(a "particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)` for `n ≥ 1`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For the one-dimensional infinite square well, the ratio of the fourth energy level to the
ground-state energy is `4² = 16`. -/
theorem box_level_4 (m L hbar : ℝ) (hm : m ≠ 0) (hL : L ≠ 0) (hbar0 : hbar ≠ 0) :
    boxEnergy m L hbar 4 / boxEnergy m L hbar 1 = (4 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  field_simp
  ring

end QPhys

