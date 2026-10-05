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

theorem prime_index_of_prime_repunit {n : ℕ} (h : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn2 : 2 ≤ n := by
    by_contra hlt
    interval_cases n <;> simp_all [Nat.not_prime_zero, Nat.not_prime_one]
  rw [Nat.prime_def_lt]
  refine ⟨hn2, ?_⟩
  intro m hm hmd
  by_contra hm1
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h' | h'
    · interval_cases m
      · exfalso
        have : n = 0 := Nat.eq_zero_of_zero_dvd hmd
        omega
      · exact absurd rfl hm1
    · exact h'
  have hdvd : repunit m ∣ repunit n := repunit_dvd_repunit hmd
  have h1 : 1 < repunit m := one_lt_repunit hm2
  have h2 : repunit m < repunit n := repunit_strictMono hm
  rcases (Nat.Prime.eq_one_or_self_of_dvd h _ hdvd) with h' | h' <;> omega

