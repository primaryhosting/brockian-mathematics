import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma sum_powerset_eq_sum_range (P : Finset ℕ) (g : Finset ℕ → ℝ) {R : ℕ}
    (hR : P.card + 1 ≤ R) :
    ∑ S ∈ P.powerset, g S = ∑ j ∈ range R, ∑ S ∈ P.powersetCard j, g S := by
  rw [Finset.sum_powerset]
  refine Finset.sum_subset (by simpa using hR) ?_
  intro j _ hj
  simp only [Finset.mem_range, not_lt] at hj
  rw [Finset.powersetCard_eq_empty.mpr (by omega)]
  simp

/-- Truncated inclusion–exclusion for a product `∏ (1 - a p)`. -/
