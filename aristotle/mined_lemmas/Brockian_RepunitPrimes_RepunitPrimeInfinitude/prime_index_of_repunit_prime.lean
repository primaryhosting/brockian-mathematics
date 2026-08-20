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

theorem prime_index_of_repunit_prime {n : ℕ} (h : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push_neg at hlt
    interval_cases n <;> exact absurd h (by decide)
  refine Nat.prime_def.mpr ⟨hn2, fun m hm => ?_⟩
  have hdvd : repunit m ∣ repunit n := repunit_dvd_repunit hm
  rcases h.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · left
    have : repunit m = repunit 1 := by simpa using h1
    exact repunit_injective this
  · right
    exact repunit_injective h1

/-!
## Which primes divide repunits

Every prime other than `2` and `5` divides some (positive-index) repunit; in particular
infinitely many primes occur as divisors of repunits.
-/

