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

/-- The `n`-th repunit `R n = 1 + 10 + ... + 10^(n-1) = (10^n - 1)/9`, i.e. the number
whose decimal expansion consists of `n` ones. -/

theorem prime_repunit_of_no_small_factor {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hs : ∀ q : ℕ, q.Prime → q ∣ repunit p → q * q ≤ repunit p → q % (2 * p) ≠ 1) :
    Nat.Prime (repunit p) := by
  rw [Nat.prime_def_le_sqrt]
  refine ⟨one_lt_repunit (by omega), ?_⟩
  intro m hm2 hmsq hmd
  have hm1 : m ≠ 1 := by omega
  have hqp : Nat.Prime m.minFac := Nat.minFac_prime hm1
  have hqd : m.minFac ∣ repunit p := (Nat.minFac_dvd m).trans hmd
  have hle : m.minFac ≤ (repunit p).sqrt := le_trans (Nat.minFac_le (by omega)) hmsq
  exact hs m.minFac hqp hqd (Nat.le_sqrt.mp hle)
    (prime_factor_mod_two_mul hp hp3 hqp hqd)

/-- **Conditional reduction of the Brockian repunit-prime conjecture.**

The infinitude of repunit primes follows from the (computationally far more tractable)
statement that for every bound `N` there is a prime `p > N` such that no prime `q` with
`q ^ 2 ≤ R p` and `q ≡ 1 (mod 2p)` divides `R p`.

Indeed, by `prime_factor_mod_two_mul` *every* prime factor of `R p` is `≡ 1 (mod 2p)`, so the
hypothesis says exactly that `R p` has no prime factor below its square root, i.e. `R p` is
prime; the search space in the hypothesis is only the arithmetic progression `1 + 2p ℕ`. -/
