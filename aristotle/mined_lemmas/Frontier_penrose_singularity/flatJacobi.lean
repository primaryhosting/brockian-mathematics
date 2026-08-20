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

def flatJacobi : NullJacobi 1 where
  rho := fun t => 1 - t
  drho := fun _ => -1
  ddrho := fun _ => 0
  hasDerivAt_rho := fun t _ => by simpa using (hasDerivAt_id t).const_sub 1
  hasDerivAt_drho := fun t _ => hasDerivAt_const t (-1)
  rho_pos := fun t ht => by show (0:ℝ) < 1 - t; linarith [ht.2]
  jacobi_nec := fun _ _ => le_rfl

/-- The affine bound of `Frontier.penrose_focal_point` is sharp: for `flatJacobi` it equals
the actual affine length `1` of the regular range. -/
