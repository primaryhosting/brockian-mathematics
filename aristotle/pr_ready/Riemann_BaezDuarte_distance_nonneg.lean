/-!
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
Statement: Baez-Duarte / Nyman-Beurling shape: in any real inner product space, the squared distance from a vector v to a subspace is nonnegative, i.e. for all reals d representing that distance, 0 <= d^2. Concretely: for all x y : Real, 0 <= (x - y)^2. (RH iff the Baez-Duarte distances d_N -> 0.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Riemann.BaezDuarte

/-- Baez-Duarte / Nyman-Beurling shape: the squared distance between two reals
(e.g. a vector and its projection onto a subspace) is nonnegative. -/
theorem distance_nonneg (x y : ℝ) : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)

end Riemann.BaezDuarte

