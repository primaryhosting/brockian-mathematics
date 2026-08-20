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

namespace Brockian.AmicableNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem isAmicablePair_thabit {k p q r : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp1 : p + 1 = 3 * 2 ^ k) (hq1 : q + 1 = 3 * 2 ^ (k + 1))
    (hr1 : r + 1 = 9 * 2 ^ (2 * k + 1)) :
    IsAmicablePair (2 ^ (k + 1) * (p * q)) (2 ^ (k + 1) * r) := by
  -- abbreviation `a = 2 ^ k`
  set a : ℕ := 2 ^ k with ha
  have ha2 : 2 ≤ a := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hpow1 : (2:ℕ) ^ (k + 1) = 2 * a := by rw [ha, pow_succ]; ring
  have hpow2 : (2:ℕ) ^ (k + 1 + 1) = 4 * a := by rw [ha, pow_succ, pow_succ]; ring
  have hq1' : q + 1 = 6 * a := by rw [hq1, hpow1]; ring
  have hr1' : r + 1 = 18 * a ^ 2 := by
    rw [hr1, ha, two_mul, pow_succ, pow_add]; ring
  -- basic primality facts
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hr2 : r ≠ 2 := by nlinarith
  have hpq : p ≠ q := by omega
  have hcop2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have hcop2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  have hcop2r : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)
  have hcoppq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hc1 : Nat.Coprime (2 ^ (k + 1)) (p * q) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.mul_right hcop2p hcop2q)
  have hc2 : Nat.Coprime (2 ^ (k + 1)) r := Nat.Coprime.pow_left _ hcop2r
  -- the two sigma values
  have hsm : sigmaOne (2 ^ (k + 1) * (p * q)) = (4 * a - 1) * (3 * a) * (6 * a) := by
    rw [sigmaOne_mul_of_coprime hc1, sigmaOne_mul_of_coprime hcoppq, sigmaOne_two_pow,
      sigmaOne_prime hp, sigmaOne_prime hq, hp1, hq1', hpow2]
    ring
  have hsn : sigmaOne (2 ^ (k + 1) * r) = (4 * a - 1) * (18 * a ^ 2) := by
    rw [sigmaOne_mul_of_coprime hc2, sigmaOne_two_pow, sigmaOne_prime hr, hr1', hpow2]
  -- the integer versions of the defining equations
  have haZ : (2:ℤ) ≤ (a : ℤ) := by exact_mod_cast ha2
  have hpZ : (p : ℤ) = 3 * (a : ℤ) - 1 := by
    have : (p : ℤ) + 1 = 3 * (a : ℤ) := by exact_mod_cast hp1
    linarith
  have hqZ : (q : ℤ) = 6 * (a : ℤ) - 1 := by
    have : (q : ℤ) + 1 = 6 * (a : ℤ) := by exact_mod_cast hq1'
    linarith
  have hrZ : (r : ℤ) = 18 * (a : ℤ) ^ 2 - 1 := by
    have : (r : ℤ) + 1 = 18 * (a : ℤ) ^ 2 := by exact_mod_cast hr1'
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- distinctness
    rw [hpow1]
    intro h
    have h' : p * q = r := by
      have h2 : 0 < 2 * a := by omega
      exact Nat.eq_of_mul_eq_mul_left h2 h
    have h'' : (p : ℤ) * q = r := by exact_mod_cast h'
    rw [hpZ, hqZ, hrZ] at h''
    nlinarith
  · rw [hsm, hpow1]
    zify [show 1 ≤ 4 * a by omega]
    rw [hpZ, hqZ, hrZ]
    ring
  · rw [hsn, hpow1]
    zify [show 1 ≤ 4 * a by omega]
    rw [hpZ, hqZ, hrZ]
    ring

/-- The classical smallest amicable pair, obtained from Thabit's rule with `k = 1`. -/
