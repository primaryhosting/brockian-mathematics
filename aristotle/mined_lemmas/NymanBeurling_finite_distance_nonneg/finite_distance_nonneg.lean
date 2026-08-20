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

/-!
# Finite Distance Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: NymanBeurling.finite_distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NymanBeurling

/-- Scalar core of the Nyman–Beurling finite-shape estimate: if `p ^ 2 ≤ u ^ 2`
then the residual `u ^ 2 - p ^ 2` is nonnegative.  (Closed by `sub_nonneg`.)
The hypothesis `0 ≤ u`, requested in the statement, turns out to be unnecessary. -/

theorem finite_distance_nonneg (u p : ℝ) (hp : p ^ 2 ≤ u ^ 2) (_hu : 0 ≤ u) :
    0 ≤ u ^ 2 - p ^ 2 :=
  sub_nonneg.mpr hp

end NymanBeurling

