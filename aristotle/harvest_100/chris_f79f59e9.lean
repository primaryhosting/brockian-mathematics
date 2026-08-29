import Mathlib

/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a one-dimensional
infinite potential well ("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For a particle in a one-dimensional infinite well (with positive reduced Planck constant,
mass and width), the ratio of the fifth energy level to the ground-state energy is `5² = 25`. -/
theorem box_level_5 (hbar m L : ℝ) (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 5 / boxEnergy hbar m L 1 = (5 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : (2 : ℝ) * m * L ^ 2 ≠ 0 := by positivity
  unfold boxEnergy
  rw [div_div_div_cancel_right₀' _ _ hden]
  push_cast
  rw [div_eq_iff (by positivity)]
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

