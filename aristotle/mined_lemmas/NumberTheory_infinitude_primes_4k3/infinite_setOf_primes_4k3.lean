/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- Every natural number congruent to `3` modulo `4` has a prime factor congruent to `3`
modulo `4`.  Indeed such a number is odd, and a product of primes all congruent to `1`
modulo `4` is again congruent to `1` modulo `4`. -/

theorem infinite_setOf_primes_4k3 : {p : ℕ | Nat.Prime p ∧ p % 4 = 3}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  obtain ⟨p, hp, hlt, hmod⟩ := infinitude_primes_4k3 N
  exact absurd (hN ⟨hp, hmod⟩) (by omega)

end NumberTheory

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

