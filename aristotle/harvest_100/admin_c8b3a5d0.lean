/-
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: the requested header is written as a plain block comment because Lean 4
-- does not permit a module docstring (`/-! ... -/`) to precede `import` commands.
import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.BaezDuarte

/-- Baez-Duarte / Nyman-Beurling shape: a squared distance is nonnegative.
For all reals `x y`, `0 ≤ (x - y) ^ 2`. -/
theorem distance_nonneg (x y : ℝ) : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)

/-- Inner-product-space form: the squared distance between two vectors of a real
inner product space (in particular, from a vector to a point of a subspace)
is nonnegative. -/
theorem dist_sq_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E) : 0 ≤ dist v w ^ 2 := sq_nonneg _

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

