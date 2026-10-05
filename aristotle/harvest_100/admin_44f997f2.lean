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
theorem distance_nonneg (x y : ℝ) : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)

/-- Any real number that represents a distance has nonnegative square; in
particular this applies to each Baez-Duarte distance `d_N`. -/
theorem sq_nonneg_of_distance (d : ℝ) : 0 ≤ d ^ 2 := sq_nonneg d

/-- The same fact in any real inner product space: the squared distance between
two vectors (e.g. a vector and its projection onto a subspace) is nonnegative. -/
theorem dist_sq_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E) : 0 ≤ dist v w ^ 2 := sq_nonneg (dist v w)

/-- The distance from a vector `v` to a subspace `S` of a real inner product
space is itself nonnegative. -/
theorem infDist_subspace_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) (S : Submodule ℝ E) :
    0 ≤ Metric.infDist v (S : Set E) :=
  Metric.infDist_nonneg

/-- **Baez-Duarte / Nyman-Beurling shape, subspace version.** In any real inner
product space, the squared distance from a vector `v` to a subspace `S` is
nonnegative. (Recall RH is equivalent to the Baez-Duarte distances `d_N`
tending to `0`.) -/
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

