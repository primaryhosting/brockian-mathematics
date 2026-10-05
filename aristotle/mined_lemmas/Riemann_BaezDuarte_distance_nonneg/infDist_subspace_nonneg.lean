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

theorem infDist_subspace_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) (S : Submodule ℝ E) :
    0 ≤ Metric.infDist v (S : Set E) :=
  Metric.infDist_nonneg

/-- **Baez-Duarte / Nyman-Beurling shape, subspace version.** In any real inner
product space, the squared distance from a vector `v` to a subspace `S` is
nonnegative. (Recall RH is equivalent to the Baez-Duarte distances `d_N`
tending to `0`.) -/
