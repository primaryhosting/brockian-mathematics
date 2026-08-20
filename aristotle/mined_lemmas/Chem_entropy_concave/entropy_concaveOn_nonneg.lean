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

namespace Chem

open scoped BigOperators

/-- The Gibbs (Shannon) entropy of a probability vector `p`:
`S(p) = -∑ i, p i * log (p i)`. -/

theorem entropy_concaveOn_nonneg {ι : Type*} [Fintype ι] :
    ConcaveOn ℝ {p : ι → ℝ | ∀ i, 0 ≤ p i} (entropy (ι := ι)) := by
  have hconv := convex_nonneg_vectors ι
  refine concaveOn_finsum hconv (fun i p => Real.negMulLog (p i)) Finset.univ (fun i _ => ?_)
  exact (Real.concaveOn_negMulLog.comp_linearMap
    (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)).subset (fun p hp => hp i) hconv

/-- **The Gibbs entropy `-∑ pᵢ log pᵢ` is concave in the probability vector.** -/
