/-
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well ("particle in a box") of width `L`,
with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For a particle in a one-dimensional infinite square well with positive mass,
width and reduced Planck constant, the ratio of the seventh energy level to the
ground-state energy is `7² = 49`. -/
theorem box_level_7 (m L hbar : ℝ) (hm : 0 < m) (hL : 0 < L) (hbar_pos : 0 < hbar) :
    boxEnergy m L hbar 7 / boxEnergy m L hbar 1 = (7 : ℝ) ^ 2 := by
  have hden : (2 * m * L ^ 2) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hb : hbar ≠ 0 := ne_of_gt hbar_pos
  unfold boxEnergy
  rw [div_div_div_cancel_right₀]
  · push_cast
    field_simp
  · exact hden

end QPhys

