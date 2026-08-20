/-!
# Completed Symmetry Half
Category: Riemann Program
Target: Riemann.functional.completed_symmetry_half
Statement: At the center of symmetry, completedRiemannZeta (1 - (1/2)) = completedRiemannZeta (1/2); i.e. the functional equation is trivially self-consistent on the critical line's real point. Prove completedRiemannZeta (1 - (1/2 : Complex)) = completedRiemannZeta (1/2 : Complex).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.functional

/-- At the centre of symmetry `s = 1/2`, the functional equation for the completed
Riemann zeta function is trivially self-consistent: `Λ(1 - 1/2) = Λ(1/2)`. -/
theorem completed_symmetry_half :
    completedRiemannZeta (1 - (1 / 2 : ℂ)) = completedRiemannZeta (1 / 2 : ℂ) := by
  norm_num

end Riemann.functional


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

