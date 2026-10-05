import Mathlib
/-!
# Box Level 4
Category: Quantum Physics
Target: QPhys.box_level_4
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

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite potential well
(a "box") of width `L`, with reduced Planck constant `hbar`:
`Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For a particle in a one-dimensional infinite well (with positive mass, width and
`ħ`), the ratio of the fourth energy level to the ground-state energy is `4² = 16`. -/
theorem box_level_4 {m L hbar : ℝ} (hm : 0 < m) (hL : 0 < L) (hbar_pos : 0 < hbar) :
    boxEnergy m L hbar 4 / boxEnergy m L hbar 1 = (4 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hb : hbar ≠ 0 := ne_of_gt hbar_pos
  have hm' : m ≠ 0 := ne_of_gt hm
  have hL' : L ≠ 0 := ne_of_gt hL
  unfold boxEnergy
  push_cast
  field_simp

end QPhys

