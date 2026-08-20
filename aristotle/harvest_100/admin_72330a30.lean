/-
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.BaezDuarte

/-- Baez-Duarte / Nyman-Beurling shape: the squared distance from a vector to a
subspace is nonnegative.  Concretely, for all reals `x y`, `0 ≤ (x - y) ^ 2`.
This is Mathlib's `sq_nonneg` applied to `x - y`. -/
theorem distance_nonneg (x y : ℝ) : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)

end Riemann.BaezDuarte


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

