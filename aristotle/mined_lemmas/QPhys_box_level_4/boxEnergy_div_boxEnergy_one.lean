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

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square well
(particle in a box) of width `L`:  `Eₙ = n² π² ħ² / (2 m L²)`, for `n = 1, 2, 3, …`. -/

theorem boxEnergy_div_boxEnergy_one (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L)
    (n : ℕ) : boxEnergy hbar m L n / boxEnergy hbar m L 1 = (n : ℝ) ^ 2 := by
  have hden : (2 : ℝ) * m * L ^ 2 ≠ 0 := by positivity
  unfold boxEnergy
  rw [div_div_div_cancel_right₀]
  · push_cast
    field_simp
  · exact hden

/-- **Infinite square well, level 4.** The ratio of the fourth energy level to the ground
state energy is `4² = 16`. -/
