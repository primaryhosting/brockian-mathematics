/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-!
## Formalizing the Mordell–Faltings statement

Faltings' theorem (the Mordell conjecture) says that a smooth projective curve of
genus at least `2` defined over `ℚ` has only finitely many rational points.

The full statement requires the genus of an arbitrary curve, which is beyond what we
prove here.  We formalize the statement for smooth plane curves, where the genus is
given by the classical degree–genus formula `g = (d-1)(d-2)/2`, we prove a general
*reduction* principle for transferring finiteness of rational points along a map with
finite fibres, and we prove the theorem outright for a genus `3` curve, the Fermat
quartic `x⁴ + y⁴ = 1`, and (via the reduction) for the curve `u⁸ + v⁸ = 1`.
-/

/-- The genus of a smooth plane curve of degree `d`, given by the degree–genus
formula `g = (d-1)(d-2)/2`. -/

theorem fermatQuarticPoints_finite : fermatQuarticPoints.Finite := by
  rw [fermatQuarticPoints_eq]
  exact (Set.finite_singleton _).insert _ |>.insert _ |>.insert _

/-- The curve `u⁸ + v⁸ = 1` has finitely many rational points, deduced from the Fermat
quartic via the reduction principle along the map `(u, v) ↦ (u², v²)`. -/
