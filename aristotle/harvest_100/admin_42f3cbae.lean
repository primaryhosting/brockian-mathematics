import Mathlib

/-!
# Box Level 6
Category: Quantum Physics
Target: QPhys.box_level_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well ("particle in a box") of width `L`,
with reduced Planck constant `hbar`:
`E n = n² π² hbar² / (2 m L²)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For the infinite square well, the ratio of the sixth energy level to the
ground-state energy is `6² = 36`. -/
theorem box_level_6 {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L) (hbar_pos : 0 < hbar) :
    boxEnergy m L hbar 6 / boxEnergy m L hbar 1 = (6 : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) * m * L ^ 2 ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hh : hbar ≠ 0 := ne_of_gt hbar_pos
  simp only [boxEnergy]
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

