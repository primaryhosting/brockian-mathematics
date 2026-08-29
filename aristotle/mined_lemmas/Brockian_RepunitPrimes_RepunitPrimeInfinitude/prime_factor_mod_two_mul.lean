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

theorem prime_factor_mod_two_mul {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hq : q.Prime) (hqd : q ∣ repunit p) : q % (2 * p) = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by rintro rfl; exact not_two_dvd_repunit (by omega) hqd
  have hq5 : q ≠ 5 := by rintro rfl; exact not_five_dvd_repunit (by omega) hqd
  have hq3 : q ≠ 3 := by
    rintro rfl
    have h1 : ((repunit p : ℕ) : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hqd
    rw [repunit_mod_three] at h1
    have h2 : (3 : ℕ) ∣ p := (ZMod.natCast_eq_zero_iff _ _).mp h1
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h2
    omega
  have hzero : ((repunit p : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hqd
  have hpow : (10 : ZMod q) ^ p = 1 := by
    have h1 : ((10 ^ p : ℕ) : ZMod q) = ((9 * repunit p + 1 : ℕ) : ZMod q) := by
      rw [nine_mul_repunit_add_one]
    push_cast at h1
    rw [hzero] at h1
    simpa using h1
  have hne0 : (10 : ZMod q) ≠ 0 := by
    intro h0
    have h10 : ((10 : ℕ) : ZMod q) = 0 := by push_cast; exact h0
    have hd : (q : ℕ) ∣ 10 := (ZMod.natCast_eq_zero_iff _ _).mp h10
    rcases prime_dvd_ten hq hd with rfl | rfl
    · exact hq2 rfl
    · exact hq5 rfl
  have hord : orderOf (10 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one hpow
  have hordp : orderOf (10 : ZMod q) = p := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hord) with h' | h'
    · exfalso
      have h10 : (10 : ZMod q) = 1 := orderOf_eq_one_iff.mp h'
      have h9 : ((9 : ℕ) : ZMod q) = 0 := by push_cast; linear_combination h10
      have hd : (q : ℕ) ∣ 9 := (ZMod.natCast_eq_zero_iff _ _).mp h9
      exact hq3 (prime_dvd_nine hq hd)
    · exact h'
  have hdvdp : p ∣ q - 1 := by
    have hfer : (10 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne0
    have := orderOf_dvd_of_pow_eq_one hfer
    rwa [hordp] at this
  have hqodd : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left hq2
  have hq1 : 1 ≤ q := hq.one_lt.le.trans' (by norm_num)
  have hdvd2 : 2 ∣ q - 1 := by omega
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  have h2p : 2 * p ∣ q - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd2 hdvdp
  obtain ⟨k, hk⟩ := h2p
  have hqk : q = 2 * p * k + 1 := by omega
  rw [hqk, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- **Primality criterion.** For a prime `p > 3`, if `R p` has no prime factor `q` with
`q * q ≤ R p` lying in the arithmetic progression `1 (mod 2p)`, then `R p` is prime.
(By `prime_factor_mod_two_mul` all prime factors of `R p` lie in that progression, so the
hypothesis really says that `R p` has no prime factor at most its square root.) -/
