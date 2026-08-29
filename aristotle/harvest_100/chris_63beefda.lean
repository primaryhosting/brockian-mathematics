/-
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
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

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square well
(a "box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The ground-state energy of the infinite well is nonzero for positive mass, width
and reduced Planck constant. -/
theorem boxEnergy_one_ne_zero {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m)
    (hL : 0 < L) : boxEnergy hbar m L 1 ≠ 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : 0 < boxEnergy hbar m L 1 := by
    unfold boxEnergy
    positivity
  exact ne_of_gt hpos

/-- **Box, level 1.** The infinite-well energy ratio `E₁ / E₁` equals `1² = 1`. -/
theorem box_level_1 {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 1 / boxEnergy hbar m L 1 = (1 : ℝ) ^ 2 := by
  rw [div_self (boxEnergy_one_ne_zero hhbar hm hL)]
  norm_num

end QPhys

