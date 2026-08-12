/-
# Completed Symmetry Half
Category: Riemann Program
Target: Riemann.functional.completed_symmetry_half
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Completed Symmetry Half

At the center of symmetry of the functional equation of the completed Riemann zeta function,
the reflection `s ↦ 1 - s` fixes the point `s = 1/2`, so the functional equation
`completedRiemannZeta (1 - s) = completedRiemannZeta s` is trivially self-consistent there.
-/

namespace Riemann.functional

/-- At the center of symmetry `s = 1/2`, the reflection `s ↦ 1 - s` is the identity, so the
completed Riemann zeta function takes the same value at `1 - 1/2` and at `1/2`. -/
theorem completed_symmetry_half :
    completedRiemannZeta (1 - (1 / 2 : ℂ)) = completedRiemannZeta (1 / 2 : ℂ) := by
  norm_num

#print axioms Riemann.functional.completed_symmetry_half

end Riemann.functional

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

