import Mathlib
/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command,
-- including module docstrings, so the header block above sits just after the
-- single `import Mathlib` line.

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck
constant `hbar`:  `Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For the one-dimensional infinite square well, the ratio of the fifth energy
level to the ground-state energy is `5² = 25`. -/
theorem box_level_5 (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 5 / boxEnergy hbar m L 1 = (5 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h : boxEnergy hbar m L 1 ≠ 0 := by
    simp only [boxEnergy, Nat.cast_one, one_pow, one_mul]
    exact div_ne_zero (by positivity) (by positivity)
  rw [div_eq_iff h]
  simp only [boxEnergy]
  push_cast
  field_simp

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

