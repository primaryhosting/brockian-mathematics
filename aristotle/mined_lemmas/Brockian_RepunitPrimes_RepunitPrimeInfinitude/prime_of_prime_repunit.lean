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

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th repunit: the base-ten number consisting of `n` digits `1`,
i.e. `repunit n = (10 ^ n - 1) / 9`. -/

theorem prime_of_prime_repunit {n : ℕ} (h : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn2 : 2 ≤ n := by
    by_contra hc
    interval_cases n <;> simp_all [Nat.not_prime_zero, Nat.not_prime_one]
  refine Nat.prime_def.mpr ⟨hn2, ?_⟩
  intro m hm
  by_contra hcon
  push_neg at hcon
  obtain ⟨hm1, hmn⟩ := hcon
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm (by omega)
  have hm2 : 2 ≤ m := by omega
  have hmlt : m < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hm) hmn
  have hdvd : repunit m ∣ repunit n := repunit_dvd_repunit hm
  rcases (Nat.Prime.eq_one_or_self_of_dvd h _ hdvd) with h1 | h2
  · exact absurd h1 (by have := one_lt_repunit hm2; omega)
  · exact absurd h2 (by have := repunit_strictMono hmlt; omega)

/-- `repunit 2 = 11` is prime, so repunit primes exist. -/
