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

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` with `p ^ 2 ∣ (p - 1)! + 1`
(the ordinary Wilson congruence `p ∣ (p-1)! + 1` holds for every prime). -/

theorem wilsonPrimes_finite_iff_bounded :
    {p : ℕ | IsWilsonPrime p}.Finite ↔ ∃ N : ℕ, ∀ p : ℕ, IsWilsonPrime p → p ≤ N := by
  rw [← Set.not_infinite, wilsonPrimes_infinite_iff_unbounded]
  push_neg
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp => hN p hp⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp => hN p hp⟩

/-- Equivalent reformulation of the conjecture in terms of Wilson quotients: there are
infinitely many Wilson primes iff for every `N` some prime `p > N` divides its Wilson
quotient `((p-1)! + 1) / p`. -/
