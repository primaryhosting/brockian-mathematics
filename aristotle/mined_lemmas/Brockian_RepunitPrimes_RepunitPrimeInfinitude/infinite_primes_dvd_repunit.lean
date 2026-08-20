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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RepunitPrimes

open Finset

/-- The `n`-th base-ten repunit `1, 11, 111, ...` (with `repunit 0 = 0`). -/

theorem infinite_primes_dvd_repunit :
    {p : ℕ | Nat.Prime p ∧ ∃ n, 0 < n ∧ p ∣ repunit n}.Infinite := by
  have hsub : ({p : ℕ | Nat.Prime p} \ {2, 5}) ⊆
      {p : ℕ | Nat.Prime p ∧ ∃ n, 0 < n ∧ p ∣ repunit n} := by
    rintro p ⟨hp, hne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact ⟨hp, exists_repunit_dvd_of_prime hp hne.1 hne.2⟩
  exact Set.Infinite.mono hsub (Nat.infinite_setOf_prime.diff (Set.toFinite _))

/-!
## The main equivalence

The Brockian repunit-prime conjecture asserts that there are arbitrarily large `n` with `Rₙ`
prime.  The theorem below shows this is equivalent to the infinitude of the *set* of repunit
primes, and (by `prime_index_of_repunit_prime`) that any such index is itself prime.
-/

/-- The set of primes that are repunits. -/
