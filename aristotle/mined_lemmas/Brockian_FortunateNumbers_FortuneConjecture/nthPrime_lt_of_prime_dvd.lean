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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Finset

/-- The `n`-th prime (`nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/

theorem nthPrime_lt_of_prime_dvd {n m q : ℕ} (hm : 1 < m)
    (hprime : (primorialOf n + m).Prime) (hq : q.Prime) (hqm : q ∣ m) : nthPrime n < q := by
  by_contra hcon
  push_neg at hcon
  have hdvd : q ∣ primorialOf n + m := Nat.dvd_add (prime_dvd_primorialOf hq hcon) hqm
  have hle : q ≤ m := Nat.le_of_dvd (by omega) hqm
  have hpos := primorialOf_pos n
  rcases hprime.eq_one_or_self_of_dvd q hdvd with h | h
  · exact hq.one_lt.ne' h
  · omega

/-- **Key criterion.** If `m > 1`, `pₙ# + m` is prime, and `m < pₙ₊₁²`, then `m` is prime.
This is the standard unconditional half of Fortune's conjecture: a composite `m` below `pₙ₊₁²`
has a prime factor `≤ pₙ`, which then also divides `pₙ# + m`. -/
