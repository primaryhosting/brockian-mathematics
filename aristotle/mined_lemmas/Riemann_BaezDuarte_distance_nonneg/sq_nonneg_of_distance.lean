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

theorem sq_nonneg_of_distance (d : ℝ) : 0 ≤ d ^ 2 := sq_nonneg d

/-- The same fact in any real inner product space: the squared distance between
two vectors (e.g. a vector and its projection onto a subspace) is nonnegative. -/
