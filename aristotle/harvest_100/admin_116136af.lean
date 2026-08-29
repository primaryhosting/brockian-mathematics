import Mathlib
/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck
constant `hbar`:  `Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The ground-state energy of the infinite well is strictly positive. -/
theorem boxEnergy_one_pos {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    0 < boxEnergy hbar m L 1 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  unfold boxEnergy
  push_cast
  positivity

/-- General level ratio for the one-dimensional infinite well: `Eₙ / E₁ = n²`. -/
theorem boxEnergy_ratio (hbar m L : ℝ) (n : ℕ) (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hhbar' : hbar ≠ 0 := hhbar.ne'
  have hden : (2 * m * L ^ 2) ≠ 0 := by positivity
  unfold boxEnergy
  rw [div_div_div_cancel_right₀ hden]
  push_cast
  rw [one_pow, one_mul]
  field_simp

/-- For a particle in a one-dimensional infinite well, the ratio of the fifth
energy level to the ground-state energy is `5² = 25`, for any positive values
of `ħ`, mass and well width. -/
theorem box_level_5 (hbar m L : ℝ) (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 5 / boxEnergy hbar m L 1 = (5 : ℝ) ^ 2 := by
  simpa using boxEnergy_ratio hbar m L 5 hhbar hm hL

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

