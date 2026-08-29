import Mathlib
/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite square well ("particle in a box") of width `L`,
with reduced Planck constant `ħ`:
`E n = n² π² ħ² / (2 m L²)`. -/

theorem box_level_3_of_pos (hbar m L : ℝ) (hhbar : 0 < hbar) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 3 / boxEnergy hbar m L 1 = 9 := by
  have h := box_level_3 hbar m L hhbar.ne' hm.ne' hL.ne'
  rw [h]
  norm_num

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

