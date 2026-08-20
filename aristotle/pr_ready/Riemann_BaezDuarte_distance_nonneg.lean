/-!
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
Statement: Baez-Duarte / Nyman-Beurling shape: in any real inner product space, the squared distance from a vector v to a subspace is nonnegative, i.e. for all reals d representing that distance, 0 <= d^2. Concretely: for all x y : Real, 0 <= (x - y)^2. (RH iff the Baez-Duarte distances d_N -> 0.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann
namespace BaezDuarte

/-- Baez-Duarte / Nyman-Beurling shape: a squared distance is nonnegative.
For all reals `x y`, `0 ≤ (x - y) ^ 2`. -/
theorem distance_nonneg (x y : Real) : 0 ≤ (x - y) ^ 2 := by
  positivity

end BaezDuarte
end Riemann


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

