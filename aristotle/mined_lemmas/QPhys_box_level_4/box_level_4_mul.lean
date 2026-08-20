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

theorem box_level_4_mul (hbar m L : ℝ) :
    boxEnergy hbar m L 4 = (4 : ℝ) ^ 2 * boxEnergy hbar m L 1 := by
  unfold boxEnergy
  push_cast
  ring

end QPhys

