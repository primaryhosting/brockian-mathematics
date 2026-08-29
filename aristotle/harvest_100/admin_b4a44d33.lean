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
("particle in a box") of width `L`:  `Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (Real.pi ^ 2 * hbar ^ 2) / (2 * m * L ^ 2)

/-- The energy of the ground state of the infinite square well is nonzero,
for positive `ħ`, `m` and `L`. -/
theorem boxEnergy_one_ne_zero {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 1 ≠ 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have : 0 < boxEnergy hbar m L 1 := by
    unfold boxEnergy
    positivity
  exact ne_of_gt this

/-- **Box Level 1.** For the one-dimensional infinite square well, the energy ratio of the
ground state to itself is `1² = 1`, matching the general law `Eₙ / E₁ = n²`. -/
theorem box_level_1 {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 1 / boxEnergy hbar m L 1 = (1 : ℝ) ^ 2 := by
  have h := boxEnergy_one_ne_zero hhbar hm hL
  field_simp

/-- The general law `Eₙ / E₁ = n²` for the infinite square well, of which `box_level_1`
is the case `n = 1`. -/
theorem boxEnergy_ratio {hbar m L : ℝ} (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) (n : ℕ) :
    boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hden : (2 * m * L ^ 2) ≠ 0 := by positivity
  have hnum : (Real.pi ^ 2 * hbar ^ 2) ≠ 0 := by positivity
  unfold boxEnergy
  field_simp
  norm_num

end QPhys

