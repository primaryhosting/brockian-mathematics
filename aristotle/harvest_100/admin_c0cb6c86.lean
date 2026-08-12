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

/-- Baez-Duarte / Nyman-Beurling shape: the squared distance from a vector to a
subspace is nonnegative. Concretely, for all reals `x y`, `0 ≤ (x - y) ^ 2`. -/
theorem distance_nonneg : ∀ x y : ℝ, 0 ≤ (x - y) ^ 2 := by
  intro x y
  positivity

/-- The inner-product-space form: in any real inner product space, for a vector `v`
and a subspace `K`, the squared distance from `v` to `K` is nonnegative. -/
theorem distance_sq_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (K : Set E) : 0 ≤ (Metric.infDist v K) ^ 2 := by
  positivity

end BaezDuarte
end Riemann

#print axioms Riemann.BaezDuarte.distance_nonneg
#print axioms Riemann.BaezDuarte.distance_sq_nonneg

