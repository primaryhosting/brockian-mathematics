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

theorem exists_repunit_dvd_of_prime {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    ∃ n, 0 < n ∧ p ∣ repunit n := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases h3 : p = 3
  · refine ⟨3, by norm_num, ?_⟩
    subst h3
    norm_num [repunit, Finset.sum_range_succ]
  -- `10` is invertible mod `p`, so `p ∣ 10 ^ (p - 1) - 1 = 9 * R_{p-1}`
  have hp10 : ¬ (p ∣ 10) := by
    intro hd
    have h1 : p ∣ 2 * 5 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  have h10 : (10 : ZMod p) ≠ 0 := by
    intro h
    refine hp10 ((ZMod.natCast_eq_zero_iff 10 p).mp ?_)
    push_cast
    exact h
  have hferm : (10 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h10
  have hdvd9 : p ∣ 9 * repunit (p - 1) := by
    have hcast : ((9 * repunit (p - 1) + 1 : ℕ) : ZMod p) = 1 := by
      rw [nine_mul_repunit_add_one]
      push_cast
      exact hferm
    have : ((9 * repunit (p - 1) : ℕ) : ZMod p) = 0 := by
      push_cast at hcast ⊢
      linear_combination hcast
    exact (ZMod.natCast_eq_zero_iff _ p).mp this
  have hp9 : ¬ (p ∣ 9) := by
    intro hd
    have h1 : p ∣ 3 ^ 2 := by norm_num; exact hd
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h1))
  have hcop : Nat.Coprime p 9 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hp9
  refine ⟨p - 1, ?_, ?_⟩
  · have := hp.two_le; omega
  · exact hcop.dvd_of_dvd_mul_left hdvd9

/-- Infinitely many primes divide some repunit. -/
