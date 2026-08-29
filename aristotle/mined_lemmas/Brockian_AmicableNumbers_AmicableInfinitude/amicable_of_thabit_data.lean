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

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction

namespace Brockian.AmicableNumbers

/-- The sum of the proper divisors of `n` (the divisors of `n` other than `n` itself). -/

theorem amicable_of_thabit_data {n p q r : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpe : p + 1 = 3 * 2 ^ n) (hqe : q + 1 = 6 * 2 ^ n)
    (hre : r + 1 = 18 * 2 ^ n * 2 ^ n) :
    Amicable (2 ^ (n + 1) * (p * q)) (2 ^ (n + 1) * r) := by
  set A := 2 ^ n with hA
  have hA2 : 2 ≤ A := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hAeven : 2 ∣ A := by
    rw [hA]
    exact dvd_pow_self 2 (by omega)
  -- oddness of `p`, `q`, `r`
  have hodd : ∀ x : ℕ, 2 ∣ x + 1 → ¬ (2 ∣ x) := by
    intro x hx hx2; omega
  have hp2 : ¬ (2 ∣ p) := by
    refine hodd p ?_
    rw [hpe]; exact Dvd.dvd.mul_left hAeven 3
  have hq2 : ¬ (2 ∣ q) := by
    refine hodd q ?_
    rw [hqe]; exact Dvd.dvd.mul_left hAeven 6
  have hr2 : ¬ (2 ∣ r) := by
    refine hodd r ?_
    rw [hre]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hAeven 18) A
  have c2p : Nat.Coprime 2 p := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hp2
  have c2q : Nat.Coprime 2 q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hq2
  have c2r : Nat.Coprime 2 r := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hr2
  have hpq : p ≠ q := by omega
  have cpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have cop1 : Nat.Coprime (2 ^ (n + 1)) (p * q) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.mul_right c2p c2q)
  have cop2 : Nat.Coprime (2 ^ (n + 1)) r := Nat.Coprime.pow_left _ c2r
  -- the divisor sum of the 2-part
  set S := ∑ d ∈ (2 ^ (n + 1)).divisors, d with hS
  have hSe : S + 1 = 4 * A := by
    have h := sum_divisors_two_pow (n + 1)
    rw [← hS] at h
    rw [h, hA]; ring
  -- divisor sums of the two candidate numbers
  have hsa : ∑ d ∈ (2 ^ (n + 1) * (p * q)).divisors, d = S * ((p + 1) * (q + 1)) := by
    rw [Nat.Coprime.sum_divisors_mul cop1, Nat.Coprime.sum_divisors_mul cpq,
      sum_divisors_prime hp, sum_divisors_prime hq]
  have hsb : ∑ d ∈ (2 ^ (n + 1) * r).divisors, d = S * (r + 1) := by
    rw [Nat.Coprime.sum_divisors_mul cop2, sum_divisors_prime hr]
  -- the key arithmetic identity: `σ(a) = σ(b) = a + b`
  have hsum : S * ((p + 1) * (q + 1)) = 2 ^ (n + 1) * (p * q) + 2 ^ (n + 1) * r ∧
      S * (r + 1) = 2 ^ (n + 1) * (p * q) + 2 ^ (n + 1) * r := by
    have hpow : (2 : ℕ) ^ (n + 1) = 2 * A := by rw [hA]; ring
    have e1 : (p : ℤ) = 3 * A - 1 := by
      have h : (p : ℤ) + 1 = 3 * (A : ℤ) := by exact_mod_cast hpe
      linarith
    have e2 : (q : ℤ) = 6 * A - 1 := by
      have h : (q : ℤ) + 1 = 6 * (A : ℤ) := by exact_mod_cast hqe
      linarith
    have e3 : (r : ℤ) = 18 * A * A - 1 := by
      have h : (r : ℤ) + 1 = 18 * (A : ℤ) * (A : ℤ) := by exact_mod_cast hre
      linarith
    have e4 : (S : ℤ) = 4 * A - 1 := by
      have h : (S : ℤ) + 1 = 4 * (A : ℤ) := by exact_mod_cast hSe
      linarith
    constructor
    · have h : (S : ℤ) * ((p + 1) * (q + 1)) = (2 * A) * (p * q) + (2 * A) * r := by
        rw [e1, e2, e3, e4]; ring
      rw [hpow]
      exact_mod_cast h
    · have h : (S : ℤ) * (r + 1) = (2 * A) * (p * q) + (2 * A) * r := by
        rw [e1, e2, e3, e4]; ring
      rw [hpow]
      exact_mod_cast h
  refine ⟨?_, ?_, ?_⟩
  · -- distinctness
    intro hcontra
    have hpos : 0 < 2 ^ (n + 1) := Nat.two_pow_pos _
    have hqr : p * q = r := Nat.eq_of_mul_eq_mul_left hpos hcontra
    have h1 : (p + 1) * (q + 1) = r + 1 := by
      rw [hpe, hqe, hre]; ring
    have h2 : p * q + p + q + 1 = r + 1 := by
      rw [← h1]; ring
    have hp2' : 2 ≤ p := hp.two_le
    omega
  · -- `σ(a) = a + b`
    have h := sum_divisors_eq (2 ^ (n + 1) * (p * q))
    rw [hsa, hsum.1] at h
    omega
  · -- `σ(b) = a + b`
    have h := sum_divisors_eq (2 ^ (n + 1) * r)
    rw [hsb, hsum.2] at h
    omega

/-- **Thabit ibn Qurra's rule.** If `n ≥ 1` and the Thabit triple at `n` consists of primes,
then `2ⁿ⁺¹·(3·2ⁿ-1)·(3·2ⁿ⁺¹-1)` and `2ⁿ⁺¹·(9·2²ⁿ⁺¹-1)` are amicable. -/
