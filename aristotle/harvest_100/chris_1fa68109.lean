import Mathlib

/-!
# Distance Nonneg
Category: Riemann Program
Target: Riemann.BaezDuarte.distance_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Riemann
namespace BaezDuarte

/-- Baez-Duarte / Nyman-Beurling shape: the squared distance between two reals
(for instance between a vector and its projection onto a subspace, measured in a
real inner product space) is nonnegative. -/
theorem distance_nonneg (x y : ℝ) : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)

/-- The same statement in a general real inner product space: for any vector `v`
and any subspace element `w`, the squared distance `‖v - w‖ ^ 2` is nonnegative. -/
theorem distance_nonneg_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : E) : 0 ≤ ‖v - w‖ ^ 2 := sq_nonneg _

end BaezDuarte
end Riemann

