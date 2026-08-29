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
def repunit (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 10 ^ i

@[simp] lemma repunit_zero : repunit 0 = 0 := rfl
@[simp] lemma repunit_one : repunit 1 = 1 := rfl

lemma repunit_succ (n : ℕ) : repunit (n + 1) = repunit n + 10 ^ n := by
  simp [repunit, Finset.sum_range_succ]

/-- The defining identity `9 * R n + 1 = 10 ^ n`. -/
lemma nine_mul_repunit_add_one (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repunit_succ, pow_succ]; omega

lemma repunit_strictMono : StrictMono repunit := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  have : 0 < 10 ^ k := pow_pos (by norm_num) _
  simp only [repunit_succ]
  omega

lemma one_lt_repunit {n : ℕ} (hn : 2 ≤ n) : 1 < repunit n := by
  calc 1 = repunit 1 := by simp
  _ < repunit n := repunit_strictMono (by omega)

/-- If `m ∣ n` then `R m ∣ R n`. -/
lemma repunit_dvd_repunit {m n : ℕ} (h : m ∣ n) : repunit m ∣ repunit n := by
  obtain ⟨k, rfl⟩ := h
  have h9 : 9 * repunit m ∣ 9 * repunit (m * k) := by
    have h1 : 9 * repunit m = 10 ^ m - 1 := by
      have := nine_mul_repunit_add_one m; omega
    have h2 : 9 * repunit (m * k) = (10 ^ m) ^ k - 1 ^ k := by
      have := nine_mul_repunit_add_one (m * k)
      rw [← pow_mul]
      simp only [one_pow]
      omega
    rw [h1, h2]
    simpa using Nat.sub_dvd_pow_sub_pow (10 ^ m) 1 k
  exact (mul_dvd_mul_iff_left (by norm_num : (9 : ℕ) ≠ 0)).mp h9

/-- If a repunit `R n` is prime, then its index `n` is prime. -/
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

lemma repunit_mod_three (n : ℕ) : ((repunit n : ℕ) : ZMod 3) = (n : ZMod 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h10 : ((10 : ZMod 3)) = 1 := by decide
      push_cast [repunit_succ] at ih ⊢
      rw [ih, h10]
      ring

lemma not_two_dvd_repunit {n : ℕ} (hn : 0 < n) : ¬ (2 ∣ repunit n) := by
  intro h
  have h1 := nine_mul_repunit_add_one n
  have h2 : (2 : ℕ) ∣ 10 ^ n := dvd_pow (by norm_num) (by omega)
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := h2
  omega

lemma not_five_dvd_repunit {n : ℕ} (hn : 0 < n) : ¬ (5 ∣ repunit n) := by
  intro h
  have h1 := nine_mul_repunit_add_one n
  have h2 : (5 : ℕ) ∣ 10 ^ n := dvd_pow (by norm_num) (by omega)
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := h2
  omega

private lemma prime_dvd_ten {q : ℕ} (hq : q.Prime) (hd : q ∣ 10) : q = 2 ∨ q = 5 := by
  have h1 := Nat.le_of_dvd (by norm_num) hd
  have h2 := hq.two_le
  interval_cases q <;> revert hd hq <;> decide

private lemma prime_dvd_nine {q : ℕ} (hq : q.Prime) (hd : q ∣ 9) : q = 3 := by
  have h1 := Nat.le_of_dvd (by norm_num) hd
  have h2 := hq.two_le
  interval_cases q <;> revert hd hq <;> decide

/-- Every prime factor `q` of `R p`, for a prime `p > 3`, satisfies `q ≡ 1 (mod 2p)`. -/
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
theorem RepunitPrimeInfinitude
    (h : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
      ∀ q : ℕ, q.Prime → q ∣ repunit p → q * q ≤ repunit p → q % (2 * p) ≠ 1) :
    {n : ℕ | Nat.Prime (repunit n)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨p, hpN, hp, hs⟩ := h (max N 3)
  have hp3 : 3 < p := lt_of_le_of_lt (le_max_right N 3) hpN
  exact ⟨p, prime_repunit_of_no_small_factor hp hp3 hs,
    lt_of_le_of_lt (le_max_left N 3) hpN⟩

/-- The hypothesis of `RepunitPrimeInfinitude` is in fact *equivalent* to the infinitude of
repunit primes: the reduction above loses nothing. -/
theorem repunitPrimes_infinite_iff :
    {n : ℕ | Nat.Prime (repunit n)}.Infinite ↔
      (∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
        ∀ q : ℕ, q.Prime → q ∣ repunit p → q * q ≤ repunit p → q % (2 * p) ≠ 1) := by
  refine ⟨fun hinf N => ?_, RepunitPrimeInfinitude⟩
  obtain ⟨p, hp, hpN⟩ := hinf.exists_gt N
  have hpprime : Nat.Prime (repunit p) := hp
  refine ⟨p, hpN, prime_index_of_prime_repunit hpprime, fun q hq hqd hqle => ?_⟩
  have hqeq : q = repunit p := (hpprime.eq_one_or_self_of_dvd q hqd).resolve_left hq.one_lt.ne'
  have h2 : 2 ≤ q := hq.two_le
  rw [← hqeq] at hqle
  nlinarith

/-- **Unconditional partial result.** Infinitely many primes divide some repunit: for every
prime `p > 3` the least prime factor of `R p` is `≡ 1 (mod 2p)`, hence exceeds `2p`. -/
theorem infinite_primes_dvd_repunit :
    {q : ℕ | q.Prime ∧ ∃ n : ℕ, 0 < n ∧ q ∣ repunit n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max N 3 + 1)
  have hp3 : 3 < p := by omega
  have hR : repunit p ≠ 1 := by
    have := one_lt_repunit (n := p) (by omega); omega
  set q := (repunit p).minFac with hqdef
  have hqp : q.Prime := Nat.minFac_prime hR
  have hqd : q ∣ repunit p := Nat.minFac_dvd _
  have hmod : q % (2 * p) = 1 := prime_factor_mod_two_mul hp hp3 hqp hqd
  have hlt : N < q := by
    have h1 : q % (2 * p) ≤ q := Nat.mod_le _ _
    rcases Nat.lt_or_ge q (2 * p) with hcase | hcase
    · rw [Nat.mod_eq_of_lt hcase] at hmod
      exact absurd hmod hqp.one_lt.ne'
    · have : N < 2 * p := by omega
      omega
  exact ⟨q, ⟨hqp, p, by omega, hqd⟩, hlt⟩

/-- The set of repunit primes is nonempty: `R 2 = 11` is prime. -/
theorem prime_repunit_two : Nat.Prime (repunit 2) := by
  have : repunit 2 = 11 := by decide
  rw [this]
  norm_num

end Brockian.RepunitPrimes

