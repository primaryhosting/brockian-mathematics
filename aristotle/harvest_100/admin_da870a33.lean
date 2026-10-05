/-
# Box Level 4
Category: Quantum Physics
Target: QPhys.box_level_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a one-dimensional
infinite potential well ("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The ground-state energy of the infinite well is positive whenever the mass, the width and
`ħ` are positive. -/
theorem boxEnergy_one_pos {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L) (hbar_pos : 0 < hbar) :
    0 < boxEnergy m L hbar 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold boxEnergy
  positivity

/-- **Infinite square well energy ratio.**  For a particle of mass `m > 0` in a box of width
`L > 0` with `ħ > 0`, the fourth level has energy `4² = 16` times the ground-state energy. -/
theorem box_level_4 {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L) (hbar_pos : 0 < hbar) :
    boxEnergy m L hbar 4 / boxEnergy m L hbar 1 = (4 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hm' : m ≠ 0 := ne_of_gt hm
  have hL' : L ≠ 0 := ne_of_gt hL
  have hb' : hbar ≠ 0 := ne_of_gt hbar_pos
  have h1 : boxEnergy m L hbar 1 ≠ 0 := ne_of_gt (boxEnergy_one_pos hm hL hbar_pos)
  rw [div_eq_iff h1]
  unfold boxEnergy
  field_simp
  ring

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

