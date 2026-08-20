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

/-- Energy levels of a quantum particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, in units where the reduced
Planck constant is `hbar`:  `E n = n² π² ħ² / (2 m L²)`. -/

theorem box_level_1 (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 1 / boxEnergy hbar m L 1 = (1 : ℝ) ^ 2 := by
  have h : boxEnergy hbar m L 1 ≠ 0 := by
    have : (0:ℝ) < Real.pi ^ 2 * hbar ^ 2 := by positivity
    unfold boxEnergy
    have h2 : (0:ℝ) < 2 * m * L ^ 2 := by positivity
    push_cast
    rw [ne_eq, div_eq_zero_iff]
    push_neg
    constructor
    · nlinarith
    · exact ne_of_gt h2
  rw [div_self h]
  norm_num

end QPhys

