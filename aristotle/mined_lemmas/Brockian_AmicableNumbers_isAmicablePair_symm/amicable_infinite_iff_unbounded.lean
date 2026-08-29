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

/-
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of all (positive) divisors of `n`.  For `n = 0` this is `0`. -/

theorem amicable_infinite_iff_unbounded :
    AmicableSet.Infinite ↔ ∀ N : ℕ, ∃ m ∈ AmicableSet, N < m := by
  constructor
  · intro h N
    by_contra hc
    push_neg at hc
    exact h (Set.Finite.subset (Set.finite_Iic N) fun m hm => hc m hm)
  · intro h hfin
    obtain ⟨N, hN⟩ := bounded_of_finite hfin
    obtain ⟨m, hm, hlt⟩ := h N
    exact absurd (hN m hm) (by omega)


/-! ### The divisor-sum function: basic multiplicative toolkit -/

/-- `sumOfDivisors` is multiplicative on coprime arguments. -/
