import Mathlib
/-!
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Riemann.BaezDuarte

/-- **Target.** Baez-Duarte / Nyman-Beurling shape: the squared distance between
two real quantities is nonnegative. Concretely, for all reals `x y`,
`0 ≤ (x - y) ^ 2`. -/

theorem infDist_subspace_sq_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) (S : Submodule ℝ E) :
    0 ≤ Metric.infDist v (S : Set E) ^ 2 :=
  sq_nonneg _

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

