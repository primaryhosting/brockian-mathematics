import Mathlib

open Finset Polynomial ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Math

/-- The sum of all `n`-th roots of unity in `ℂ` is `0`, for `1 < n`. -/

lemma sum_divisors_sum_primitiveRoots (n : ℕ) :
    ∑ d ∈ n.divisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ = ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ζ := by
  classical
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, Finset.sum_biUnion]
  intro i _ j _ hij
  exact IsPrimitiveRoot.disjoint hij

/-- The sum of the primitive `9`-th roots of unity equals `μ 9` (which is `0`). -/
