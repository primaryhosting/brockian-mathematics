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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GilbreathConjecture

/-! ## Primes -/

/-- `n` is prime: it is at least `2` and has no divisor `d` with `2 ≤ d < n`. -/

theorem isPrimeEnumeration_nth_prime : IsPrimeEnumeration (Nat.nth Nat.Prime) := by
  refine ⟨fun n => isPrimeNat_iff_prime.2 (Nat.prime_nth_prime n), ?_, ?_⟩
  · intro i j hij
    exact (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 hij
  · intro q hq
    exact ⟨Nat.count Nat.Prime q, Nat.nth_count (isPrimeNat_iff_prime.1 hq)⟩

/-- An increasing enumeration of the primes exists, so the hypothesis
`IsPrimeEnumeration` of `GilbreathConjecture` is satisfiable. -/
