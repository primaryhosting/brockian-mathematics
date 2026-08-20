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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.ZumkellerNumbers

/-- A natural number `n` is *Zumkeller* if it is positive and its set of divisors can be
split into two parts with equal sums. -/

theorem prod_primeFactors_le {n : ℕ} (hodd : Odd n) (hcard : n.primeFactors.card ≤ 2) :
    (∏ p ∈ n.primeFactors, p) ≤ 2 * ∏ p ∈ n.primeFactors, (p - 1) := by
  have hodd' : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, rfl⟩ := hdvd
      rw [Nat.odd_iff] at hodd
      omega
    have := hprime.two_le
    omega
  interval_cases hc : n.primeFactors.card
  · rw [Finset.card_eq_zero] at hc
    simp [hc]
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hp3 : 3 ≤ p := hodd' p (by simp [hp])
    simp only [hp, Finset.prod_singleton]
    omega
  · obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc
    have hp3 : 3 ≤ p := hodd' p (by simp [hset])
    have hq3 : 3 ≤ q := hodd' q (by simp [hset])
    have hpprime := Nat.prime_of_mem_primeFactors (show p ∈ n.primeFactors by simp [hset])
    have hqprime := Nat.prime_of_mem_primeFactors (show q ∈ n.primeFactors by simp [hset])
    have hp4 : p ≠ 4 := by rintro rfl; norm_num at hpprime
    have hq4 : q ≠ 4 := by rintro rfl; norm_num at hqprime
    -- distinct odd primes, so one of them is `≥ 5`
    have hp5 : 5 ≤ p ∨ 5 ≤ q := by omega
    rw [hset, Finset.prod_pair hpq, Finset.prod_pair hpq]
    rcases hp5 with h5 | h5
    · nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega),
        Nat.sub_add_cancel (show 1 ≤ q by omega)]
    · nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega),
        Nat.sub_add_cancel (show 1 ≤ q by omega)]

/-- An odd number with at most two distinct prime factors is deficient: `σ n < 2 * n`. -/
