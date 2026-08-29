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

theorem dist_sq_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E) : 0 ≤ dist v w ^ 2 := sq_nonneg (dist v w)

/-- The distance from a vector `v` to a subspace `S` of a real inner product
space is itself nonnegative. -/
