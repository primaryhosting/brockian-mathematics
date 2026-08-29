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

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite square well
of width `L`:  `Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (ħ m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * ħ ^ 2 / (2 * m * L ^ 2)

/-- For the one-dimensional infinite square well, the ratio of the seventh energy level
to the ground-state energy is `7² = 49`. -/
theorem box_level_7 (ħ m L : ℝ) (hħ : ħ ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy ħ m L 7 / boxEnergy ħ m L 1 = (7 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
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

