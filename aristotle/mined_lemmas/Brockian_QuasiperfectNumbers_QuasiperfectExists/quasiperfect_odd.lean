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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of its divisors equals `2 * n + 1`,
i.e. the sum of its proper divisors is `n + 1`. -/

theorem quasiperfect_odd {n : ℕ} (hn : 0 < n) (h : Quasiperfect n) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  swap
  · exact ho
  exfalso
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exfalso
      rw [hk, pow_zero, one_mul] at hnm
      rw [hnm] at he
      exact (Nat.not_odd_iff_even.mpr he) hm
    · exact hk
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hmul : ArithmeticFunction.sigma 1 n
      = ArithmeticFunction.sigma 1 (2 ^ k) * ArithmeticFunction.sigma 1 m := by
    rw [hnm]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  set d := ArithmeticFunction.sigma 1 (2 ^ k) with hd
  have hd1 : d + 1 = 2 ^ (k + 1) := sigma_two_pow k
  have heq : d * ArithmeticFunction.sigma 1 m = 2 * (2 ^ k * m) + 1 := by
    rw [← hmul, h, hnm]
  have e1 : 2 * (2 ^ k * m) = (d + 1) * m := by rw [hd1]; ring
  rw [e1] at heq
  have hdm : d * ArithmeticFunction.sigma 1 m = d * m + (m + 1) := by rw [heq]; ring
  have hdvd : d ∣ m + 1 := by
    have h3 : d ∣ d * ArithmeticFunction.sigma 1 m - d * m := Nat.dvd_sub ⟨_, rfl⟩ ⟨_, rfl⟩
    have h4 : d * ArithmeticFunction.sigma 1 m - d * m = m + 1 := by omega
    rwa [h4] at h3
  have hsodd : Odd (ArithmeticFunction.sigma 1 m) := by
    have hodd_total : Odd (ArithmeticFunction.sigma 1 n) := by rw [h]; exact ⟨n, by ring⟩
    rw [hmul] at hodd_total
    exact (Nat.odd_mul.mp hodd_total).2
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  obtain ⟨t, ht⟩ := isSquare_of_odd_of_odd_sigma hm0 hm hsodd
  have hd4 : d % 4 = 3 := by
    have h4 : (4 : ℕ) ∣ 2 ^ (k + 1) := by
      refine ⟨2 ^ (k - 1), ?_⟩
      rw [show k + 1 = 2 + (k - 1) by omega, pow_add]
      norm_num
    omega
  obtain ⟨q, hq, hqd, hq4⟩ := exists_prime_factor_three_mod_four d hd4
  have hqm : q ∣ t ^ 2 + 1 := by
    have hqm' : q ∣ m + 1 := hqd.trans hdvd
    rwa [ht, ← pow_two] at hqm'
  exact not_dvd_sq_add_one hq hq4 hqm

/-- A quasiperfect number is a perfect square. -/
