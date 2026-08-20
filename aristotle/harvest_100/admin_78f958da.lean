import Mathlib

/-!
# Completed Symmetry Half
Category: Riemann Program
Target: Riemann.functional.completed_symmetry_half
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann
namespace functional

/-- At the center of symmetry `s = 1/2`, the functional equation
`completedRiemannZeta (1 - s) = completedRiemannZeta s` is self-consistent:
`completedRiemannZeta (1 - 1/2) = completedRiemannZeta (1/2)`.

This follows from `completedRiemannZeta_one_sub` (Mathlib's functional equation), but is
also immediate since `1 - (1/2 : ℂ) = 1/2`. -/
theorem completed_symmetry_half :
    completedRiemannZeta (1 - (1 / 2 : ℂ)) = completedRiemannZeta (1 / 2 : ℂ) := by
  exact completedRiemannZeta_one_sub (1 / 2 : ℂ)

end functional
end Riemann

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

