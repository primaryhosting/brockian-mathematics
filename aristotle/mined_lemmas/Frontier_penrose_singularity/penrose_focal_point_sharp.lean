import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
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

namespace Frontier

/-!
## Setting

Mathlib does not (yet) contain Lorentzian causal theory, so the Penrose singularity

theorem penrose_focal_point_sharp :
    -flatJacobi.rho 0 / flatJacobi.drho 0 = 1 := by
  show -(1 - (0 : ℝ)) / (-1) = 1
  norm_num

end Frontier

#print axioms Frontier.penrose_singularity
#print axioms Frontier.penrose_null_geodesically_incomplete
#print axioms Frontier.penrose_focal_point
#print axioms Frontier.penrose_focal_point_incomplete

