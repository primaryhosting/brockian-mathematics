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
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square
well ("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The ground-state energy of the infinite square well is positive, for a particle
of positive mass in a well of positive width, with `ħ > 0`. -/
theorem boxEnergy_one_pos {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L) (hh : 0 < hbar) :
    0 < boxEnergy m L hbar 1 := by
  have hpi := Real.pi_pos
  unfold boxEnergy
  positivity

/-- **Box Level 1.** The infinite-well energy ratio `E₁ / E₁` equals `1²`. -/
theorem box_level_1 {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L) (hh : 0 < hbar) :
    boxEnergy m L hbar 1 / boxEnergy m L hbar 1 = (1 : ℝ) ^ 2 := by
  rw [div_self (boxEnergy_one_pos hm hL hh).ne', one_pow]

/-- More generally, the level ratio `Eₙ / E₁` equals `n²`. -/
theorem boxEnergy_ratio {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L) (hh : 0 < hbar)
    (n : ℕ) : boxEnergy m L hbar n / boxEnergy m L hbar 1 = (n : ℝ) ^ 2 := by
  have hpi := Real.pi_pos
  have hden : (2 * m * L ^ 2) ≠ 0 := by positivity
  have hnum : Real.pi ^ 2 * hbar ^ 2 ≠ 0 := by positivity
  unfold boxEnergy
  field_simp
  ring

end QPhys

