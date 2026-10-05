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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Whether there are infinitely many Mersenne primes is a well-known open problem, so no
unconditional proof is attempted here.  What is proved is an *unconditional equivalence*:

  there are infinitely many Mersenne primes  ↔  there are infinitely many even perfect numbers.

The equivalence rests on the Euclid–Euler theorem, which is developed from scratch below
(`Brockian.MersennePerfect.even_and_perfect_iff`), together with an explicit size estimate
translating "unboundedly large even perfect numbers" into "unboundedly large Mersenne
exponents".

The main statement `Brockian.MersennePerfect.MersennePrimeInfinitude` is this equivalence.
Two conditional corollaries are also recorded.
-/

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset

open scoped sigma

/-- The set of exponents `p` for which `mersenne p = 2 ^ p - 1` is prime. -/
def MersenneExponents : Set ℕ := {p : ℕ | (mersenne p).Prime}

/-- The set of Mersenne primes themselves. -/
def MersennePrimes : Set ℕ := {q : ℕ | ∃ p : ℕ, q = mersenne p ∧ (mersenne p).Prime}

/-- The set of even perfect numbers. -/
def EvenPerfects : Set ℕ := {n : ℕ | Even n ∧ n.Perfect}

/-! ### The Euclid–Euler theorem -/

theorem sigma_one_two_pow (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  simp [mersenne, Nat.geomSum_eq]

/-- Euclid's direction: if `2 ^ (k+1) - 1` is prime then `2 ^ k * (2 ^ (k+1) - 1)` is perfect. -/
theorem perfect_two_pow_mul_mersenne {k : ℕ} (hp : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  have hodd : Odd (mersenne (k + 1)) := by simp
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm, isMultiplicative_sigma.map_mul_of_coprime (hodd.coprime_two_right.pow_right _),
    sigma_one_two_pow]
  · simp [hp, sigma_one_apply]
  · positivity

theorem exponent_ne_zero_of_prime_mersenne {k : ℕ} (hp : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  rintro rfl
  simp [mersenne, Nat.not_prime_one] at hp

theorem even_two_pow_mul_mersenne {k : ℕ} (hp : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  have hk := exponent_ne_zero_of_prime_mersenne hp
  simp [hk, parity_simps]

theorem exists_eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) :
    ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬ Even m := by
  refine ⟨n.factorization 2, n / 2 ^ n.factorization 2,
    (Nat.ordProj_mul_ordCompl_eq_self n 2).symm, ?_⟩
  rw [even_iff_two_dvd]
  exact Nat.not_dvd_ordCompl Nat.prime_two hpos.ne'

/-- Euler's direction: every even perfect number has the shape `2 ^ k * (2 ^ (k+1) - 1)` with
`2 ^ (k+1) - 1` prime. -/
theorem eq_two_pow_mul_mersenne_of_even_perfect {n : ℕ} (hev : Even n) (hperf : n.Perfect) :
    ∃ k : ℕ, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := hperf.2
  obtain ⟨k, m, rfl, hm⟩ := exists_eq_two_pow_mul_odd hpos
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_one_two_pow, ← mul_assoc, ← pow_succ'] at hperf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ hperf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at hperf
  have h := mul_left_cancel₀ (by positivity) hperf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  rcases Nat.sum_properDivisors_dvd (by rw [hj]; exact Dvd.intro_left (mersenne (k + 1)) rfl) with
    h1 | h1
  · have j1 : j = 1 := hj.symm.trans h1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h1
    simp [h1, j1]
  · exfalso
    have jcon := hj.symm.trans h1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have hj0 : j ≠ 0 := by
      rintro rfl
      simp at hm
    have jcon2 := mul_right_cancel₀ hj0 jcon
    match k with
    | 0 =>
      apply hm
      rw [← jcon2, pow_zero, one_mul, one_mul] at hev
      rw [← jcon2, one_mul]
      exact even_iff_two_dvd.mp hev
    | .succ k =>
      exact absurd jcon2.symm (one_lt_mersenne.mpr (by omega)).ne'

/-- The Euclid–Euler theorem characterising even perfect numbers. -/
theorem even_and_perfect_iff {n : ℕ} :
    (Even n ∧ n.Perfect) ↔ ∃ k : ℕ, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) :=
  ⟨fun ⟨hev, hperf⟩ => eq_two_pow_mul_mersenne_of_even_perfect hev hperf,
    fun ⟨_, hp, hn⟩ => hn ▸ ⟨even_two_pow_mul_mersenne hp, perfect_two_pow_mul_mersenne hp⟩⟩

/-! ### Size estimates -/

theorem self_le_mersenne (p : ℕ) : p ≤ mersenne p := by
  have h : p < 2 ^ p := Nat.lt_two_pow_self
  simp only [mersenne]
  omega

theorem two_pow_mul_mersenne_lt (k : ℕ) : 2 ^ k * mersenne (k + 1) < 2 ^ (2 * k + 1) := by
  have h : mersenne (k + 1) < 2 ^ (k + 1) := by
    have : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
    simp only [mersenne]
    omega
  calc 2 ^ k * mersenne (k + 1) < 2 ^ k * 2 ^ (k + 1) := by gcongr
    _ = 2 ^ (2 * k + 1) := by rw [← pow_add]; ring_nf

/-! ### The main equivalence -/

/-- **Mersenne prime infinitude, reduced to even perfect numbers.**

There are infinitely many Mersenne primes if and only if there are infinitely many even
perfect numbers.  (Both sides are open problems; the content here is the unconditional
equivalence, via the Euclid–Euler theorem.) -/
theorem MersennePrimeInfinitude : MersenneExponents.Infinite ↔ EvenPerfects.Infinite := by
  rw [Set.infinite_iff_exists_gt, Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨p, hp, hNp⟩ := h N
    have hp' : (mersenne p).Prime := hp
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := by
      cases p with
      | zero => simp [mersenne, Nat.not_prime_zero] at hp'
      | succ k => exact ⟨k, rfl⟩
    refine ⟨2 ^ k * mersenne (k + 1), ⟨even_two_pow_mul_mersenne hp',
      perfect_two_pow_mul_mersenne hp'⟩, ?_⟩
    calc N < k + 1 := hNp
      _ ≤ mersenne (k + 1) := self_le_mersenne _
      _ ≤ 2 ^ k * mersenne (k + 1) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
  · intro h N
    obtain ⟨n, ⟨hev, hperf⟩, hNn⟩ := h (2 ^ (2 * N + 1))
    obtain ⟨k, hk, rfl⟩ := eq_two_pow_mul_mersenne_of_even_perfect hev hperf
    have hlt : 2 ^ (2 * N + 1) < 2 ^ (2 * k + 1) := lt_trans hNn (two_pow_mul_mersenne_lt k)
    have : 2 * N + 1 < 2 * k + 1 := by
      by_contra hcon
      exact absurd (Nat.pow_le_pow_right (by norm_num) (by omega)) (not_le.mpr hlt)
    exact ⟨k + 1, hk, by omega⟩

/-- The set of Mersenne primes is infinite exactly when the set of their exponents is. -/
theorem mersennePrimes_infinite_iff : MersennePrimes.Infinite ↔ MersenneExponents.Infinite := by
  have himg : MersennePrimes = mersenne '' MersenneExponents := by
    ext q
    constructor
    · rintro ⟨p, rfl, hp⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, rfl, hp⟩
  rw [himg, Set.infinite_image_iff (strictMono_mersenne.injective.injOn)]

/-- Conditional corollary: infinitely many even perfect numbers gives infinitely many
Mersenne primes. -/
theorem mersennePrimes_infinite_of_evenPerfects_infinite (h : EvenPerfects.Infinite) :
    MersennePrimes.Infinite :=
  mersennePrimes_infinite_iff.mpr (MersennePrimeInfinitude.mpr h)

/-- Conditional corollary: if there are arbitrarily large even perfect numbers, then there are
infinitely many Mersenne primes. -/
theorem mersennePrimes_infinite_of_evenPerfects_unbounded
    (h : ∀ N : ℕ, ∃ n ∈ EvenPerfects, N < n) : MersennePrimes.Infinite :=
  mersennePrimes_infinite_of_evenPerfects_infinite (Set.infinite_of_forall_exists_gt h)

/-! ### Sanity checks

The first few Mersenne exponents and the even perfect numbers they produce. -/

example : 2 ∈ MersenneExponents := by norm_num [MersenneExponents, mersenne]

example : 3 ∈ MersenneExponents := by norm_num [MersenneExponents, mersenne]

example : 5 ∈ MersenneExponents := by norm_num [MersenneExponents, mersenne]

example : (6 : ℕ) ∈ EvenPerfects := by
  refine ⟨by decide, ?_⟩
  rw [Nat.perfect_iff_sum_properDivisors (by norm_num)]
  decide

example : (28 : ℕ) ∈ EvenPerfects := by
  refine ⟨by decide, ?_⟩
  rw [Nat.perfect_iff_sum_properDivisors (by norm_num)]
  decide

example : (496 : ℕ) ∈ EvenPerfects :=
  even_and_perfect_iff.mpr ⟨4, by norm_num [mersenne], by norm_num [mersenne]⟩

end Brockian.MersennePerfect

