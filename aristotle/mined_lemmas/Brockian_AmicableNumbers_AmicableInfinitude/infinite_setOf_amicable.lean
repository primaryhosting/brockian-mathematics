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

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem infinite_setOf_amicable
    (H : ∀ N : ℕ, ∃ k, N ≤ k ∧ Nat.Prime (3 * 2 ^ k - 1) ∧ Nat.Prime (3 * 2 ^ (k + 1) - 1) ∧
      Nat.Prime (9 * 2 ^ (2 * k + 1) - 1)) :
    {m : ℕ | ∃ n, IsAmicablePair m n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨m, n, hN, hmn⟩ := AmicableInfinitude H N
  exact ⟨m, ⟨n, hmn⟩, hN⟩

end Brockian.AmicableNumbers

section AxiomCheck
#print axioms Brockian.AmicableNumbers.AmicableInfinitude
#print axioms Brockian.AmicableNumbers.isAmicablePair_220_284
#print axioms Brockian.AmicableNumbers.infinite_setOf_amicable
end AxiomCheck

