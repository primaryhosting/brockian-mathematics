import Mathlib
/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well ("particle in a box") of width `L`,
with reduced Planck constant `ħ`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The energy of level `n` is `n²` times the ground-state energy. -/
theorem boxEnergy_eq_sq_mul_ground (hbar m L : ℝ) (n : ℕ) :
    boxEnergy hbar m L n = (n : ℝ) ^ 2 * boxEnergy hbar m L 1 := by
  unfold boxEnergy
  push_cast
  ring

/-- The ground-state energy is nonzero whenever `ħ`, `m` and `L` are. -/
theorem boxEnergy_one_ne_zero (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 1 ≠ 0 := by
  unfold boxEnergy
  simp [hhbar, hm, hL, Real.pi_ne_zero]

/-- The ratio of the `n`-th to the ground-state energy of the infinite square
well is `n²`, for any nonzero values of `ħ`, `m` and `L`. -/
theorem boxEnergy_ratio (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) (n : ℕ) :
    boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  rw [boxEnergy_eq_sq_mul_ground hbar m L n, mul_div_assoc,
    div_self (boxEnergy_one_ne_zero hbar m L hhbar hm hL), mul_one]

/-- **Infinite square well, level 3.** The ratio of the third energy level to
the ground-state energy of a particle in a one-dimensional infinite well is
`3² = 9`, independently of the mass, the well width and `ħ`. -/
theorem box_level_3 (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 3 / boxEnergy hbar m L 1 = 3 ^ 2 := by
  have h := boxEnergy_ratio hbar m L hhbar hm hL 3
  norm_num at h
  rw [h]
  norm_num

/-- Physical restatement of `box_level_3`: for strictly positive `ħ`, `m`, `L`,
the third level of the infinite square well lies at nine times the ground-state
energy. -/
theorem box_level_3_of_pos (hbar m L : ℝ) (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 3 / boxEnergy hbar m L 1 = 9 := by
  have h := box_level_3 hbar m L hhbar.ne' hm.ne' hL.ne'
  rw [h]
  norm_num

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

