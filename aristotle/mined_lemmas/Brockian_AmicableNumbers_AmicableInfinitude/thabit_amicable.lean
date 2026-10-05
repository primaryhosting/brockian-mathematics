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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset

/-- The sum of the proper divisors of `n`. -/

theorem thabit_amicable {m p q r : ℕ} (hm : 1 ≤ m)
    (hp : p + 1 = 3 * 2 ^ m) (hq : q + 1 = 3 * 2 ^ (m + 1))
    (hr : r + 1 = 9 * 2 ^ (2 * m + 1))
    (hpp : p.Prime) (hqp : q.Prime) (hrp : r.Prime) :
    IsAmicablePair (2 ^ (m + 1) * p * q) (2 ^ (m + 1) * r) := by
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by
    have : (2:ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    omega
  have hr2 : r ≠ 2 := by
    have : (2:ℕ) ^ (2 * m + 1) = 2 * (2 ^ m) ^ 2 := by
      rw [pow_succ, mul_comm 2 m, pow_mul]; ring
    nlinarith [h2m]
  have hpq : p ≠ q := by
    have : (2:ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    omega
  -- coprimality of the three prime factors
  have cop2p : Nat.Coprime (2 ^ (m + 1)) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hpp).mpr (Ne.symm hp2))
  have cop2q : Nat.Coprime (2 ^ (m + 1)) q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hqp).mpr (Ne.symm hq2))
  have cop2r : Nat.Coprime (2 ^ (m + 1)) r :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hrp).mpr (Ne.symm hr2))
  have coppq : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).mpr hpq
  -- the two divisor sums, in factored form
  set S := ∑ d ∈ ((2:ℕ) ^ (m + 1)).divisors, d
  have hS : S + 1 = 2 ^ (m + 2) := sum_divisors_two_pow (m + 1)
  have hsa : ∑ d ∈ (2 ^ (m + 1) * p * q).divisors, d = S * (p + 1) * (q + 1) := by
    rw [Nat.Coprime.sum_divisors_mul (Nat.Coprime.mul_left cop2q coppq),
      Nat.Coprime.sum_divisors_mul cop2p, sum_divisors_prime hpp, sum_divisors_prime hqp]
  have hsb : ∑ d ∈ (2 ^ (m + 1) * r).divisors, d = S * (r + 1) := by
    rw [Nat.Coprime.sum_divisors_mul cop2r, sum_divisors_prime hrp]
  -- the arithmetic identities, checked over ℤ
  have e2 : ((2:ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 := by
    rw [pow_succ, mul_comm 2 m, pow_mul]; ring
  have hpz : (p : ℤ) = 3 * 2 ^ m - 1 := by have := hp; zify at this; linarith
  have hqz : (q : ℤ) = 6 * 2 ^ m - 1 := by
    have := hq; zify at this; ring_nf at this ⊢; linarith
  have hrz : (r : ℤ) = 18 * (2 ^ m) ^ 2 - 1 := by
    have := hr; zify at this; rw [e2] at this; linarith
  have hSz : (S : ℤ) = 4 * 2 ^ m - 1 := by
    have e : ((2:ℤ) ^ (m + 2)) = 4 * 2 ^ m := by ring
    have := hS; zify at this; rw [e] at this; linarith
  have key : S * (p + 1) * (q + 1) = 2 ^ (m + 1) * p * q + 2 ^ (m + 1) * r ∧
      S * (r + 1) = 2 ^ (m + 1) * p * q + 2 ^ (m + 1) * r := by
    constructor <;> · zify
                      have e : ((2:ℤ) ^ (m + 1)) = 2 * 2 ^ m := by ring
                      rw [hpz, hqz, hrz, hSz, e]; ring
  -- the two numbers are distinct
  have hne : 2 ^ (m + 1) * p * q ≠ 2 ^ (m + 1) * r := by
    have h2mz : (2:ℤ) ≤ 2 ^ m := by exact_mod_cast h2m
    intro h
    have h' : ((2:ℤ) ^ (m + 1) * p * q) = 2 ^ (m + 1) * r := by exact_mod_cast h
    rw [hpz, hqz, hrz] at h'
    have hpos : (0:ℤ) < 2 ^ (m + 1) := by positivity
    nlinarith [h', hpos, h2mz]
  refine ⟨hne, ?_, ?_⟩
  · have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := 2 ^ (m + 1) * p * q)
    rw [hsa, key.1] at this
    unfold properDivisorSum
    omega
  · have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := 2 ^ (m + 1) * r)
    rw [hsb, key.2] at this
    unfold properDivisorSum
    omega

/-- Thâbit's rule in the form of the `ThabitTriple` predicate. -/
