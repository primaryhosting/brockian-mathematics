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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A natural number `n` is *`k`-hyperperfect* (for `k ≥ 1`) when

  `n = 1 + k * (σ n - n - 1)`,

where `σ n` is the sum of the divisors of `n`; equivalently (avoiding truncated
subtraction) `n + k * (n + 1) = 1 + k * σ n`.  The `1`-hyperperfect numbers are
exactly the perfect numbers.  It is an open conjecture that there are infinitely
many hyperperfect numbers.

This file gives a Lean-checked **conditional reduction** of that conjecture to a
Bunyakovsky-type prime hypothesis: if there are infinitely many primes `p` for
which `p² - p + 1` is also prime, then there are infinitely many hyperperfect
numbers.  The construction is explicit: for such a `p`, the number
`n = p * (p² - p + 1)` is `(p - 1)`-hyperperfect (e.g. `p = 2` gives the perfect
number `6`, `p = 3` gives `21`, `p = 7` gives `301`).
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is `k`-hyperperfect: `k ≥ 1`, `n ≥ 2`, and `n = 1 + k * (σ n - n - 1)`,
written without truncated subtraction as `n + k * (n + 1) = 1 + k * σ n`. -/
def IsHyperperfectWith (k n : ℕ) : Prop :=
  1 ≤ k ∧ 2 ≤ n ∧ n + k * (n + 1) = 1 + k * sigma1 n

/-- `n` is hyperperfect if it is `k`-hyperperfect for some `k ≥ 1`. -/
def IsHyperperfect (n : ℕ) : Prop := ∃ k, IsHyperperfectWith k n

/-- The set of hyperperfect numbers. -/
def hyperperfectSet : Set ℕ := {n | IsHyperperfect n}

/-- The candidate partner of a prime `p`: `p² - p + 1`. -/
def brockPartner (p : ℕ) : ℕ := p * p - p + 1

/-- Sum of divisors of a product of two distinct primes. -/
theorem sigma1_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    sigma1 (p * q) = (1 + p) * (1 + q) := by
  rw [sigma1, Nat.Coprime.sum_divisors_mul ((Nat.coprime_primes hp hq).mpr hpq),
    hp.divisors, hq.divisors, Finset.sum_pair hp.ne_one.symm, Finset.sum_pair hq.ne_one.symm]

/-- **Construction.** If `p` and `p² - p + 1` are both prime, then
`p * (p² - p + 1)` is `(p - 1)`-hyperperfect. -/
theorem isHyperperfectWith_brock {p : ℕ} (hp : p.Prime) (hq : (brockPartner p).Prime) :
    IsHyperperfectWith (p - 1) (p * brockPartner p) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp.two_le
  have hqval : brockPartner (2 + m) = m * m + 3 * m + 3 := by
    have h : (2 + m) * (2 + m) = (m * m + 3 * m + 3) + (2 + m) - 1 := by ring_nf; omega
    simp only [brockPartner]
    omega
  have hne : (2 + m) ≠ brockPartner (2 + m) := by rw [hqval]; omega
  refine ⟨by omega, ?_, ?_⟩
  · have h1 : 1 ≤ brockPartner (2 + m) := by omega
    calc 2 ≤ 2 + m := by omega
    _ = (2 + m) * 1 := by ring
    _ ≤ (2 + m) * brockPartner (2 + m) := Nat.mul_le_mul_left _ h1
  · rw [sigma1_mul_of_primes hp hq hne, hqval]
    have hk : 2 + m - 1 = 1 + m := by omega
    rw [hk]
    ring

/-- If `p` and `p² - p + 1` are both prime then `p * (p² - p + 1)` is hyperperfect. -/
theorem isHyperperfect_brock {p : ℕ} (hp : p.Prime) (hq : (brockPartner p).Prime) :
    IsHyperperfect (p * brockPartner p) :=
  ⟨p - 1, isHyperperfectWith_brock hp hq⟩

/-- The Bunyakovsky-type hypothesis: there are infinitely many primes `p` such that
`p² - p + 1` is also prime. -/
def InfinitelyManyBrockPrimes : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (brockPartner p).Prime

/-- **Hyperperfect Infinitude (conditional).**  If there are infinitely many primes `p`
with `p² - p + 1` prime, then there are infinitely many hyperperfect numbers. -/
theorem HyperperfectInfinitude (H : InfinitelyManyBrockPrimes) :
    hyperperfectSet.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hNp, hp, hq⟩ := H N
  refine ⟨p * brockPartner p, isHyperperfect_brock hp hq, ?_⟩
  have h1 : 1 ≤ brockPartner p := by simp [brockPartner]
  calc N < p := hNp
  _ = p * 1 := by ring
  _ ≤ p * brockPartner p := Nat.mul_le_mul_left _ h1

/-! ## A second reduction: Mersenne primes

Since the `1`-hyperperfect numbers are exactly the perfect numbers, the (also open)
infinitude of Mersenne primes likewise implies the infinitude of hyperperfect numbers.
-/

/-- `σ (2 ^ k) = 2 ^ (k + 1) - 1`. -/
theorem sigma1_two_pow (k : ℕ) : sigma1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigma1, Nat.sum_divisors_prime_pow Nat.prime_two]
  simp [Nat.geomSum_eq]

/-- `σ` of a Euclid number `2 ^ k * (2 ^ (k+1) - 1)` with the Mersenne factor prime. -/
theorem sigma1_euclid {k : ℕ} (hq : (2 ^ (k + 1) - 1).Prime) :
    sigma1 (2 ^ k * (2 ^ (k + 1) - 1)) = (2 ^ (k + 1) - 1) * (1 + (2 ^ (k + 1) - 1)) := by
  have h1 : 2 ≤ 2 ^ (k + 1) := Nat.one_lt_two_pow (by omega)
  have hodd : ¬ (2 ∣ (2 ^ (k + 1) - 1)) := by
    have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
    omega
  have hcop : Nat.Coprime (2 ^ k) (2 ^ (k + 1) - 1) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  rw [sigma1, Nat.Coprime.sum_divisors_mul hcop, ← sigma1, sigma1_two_pow,
    hq.divisors, Finset.sum_pair hq.ne_one.symm]

/-- **Euclid's construction.** If `2 ^ (k+1) - 1` is prime and `k ≥ 1`, then the perfect
number `2 ^ k * (2 ^ (k+1) - 1)` is `1`-hyperperfect. -/
theorem isHyperperfectWith_one_euclid {k : ℕ} (hk : 1 ≤ k) (hq : (2 ^ (k + 1) - 1).Prime) :
    IsHyperperfectWith 1 (2 ^ k * (2 ^ (k + 1) - 1)) := by
  have h4 : 4 ≤ 2 ^ (k + 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpk : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hdouble : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
  refine ⟨le_refl _, ?_, ?_⟩
  · calc (2 : ℕ) ≤ 2 ^ k := hpk
    _ = 2 ^ k * 1 := by ring
    _ ≤ 2 ^ k * (2 ^ (k + 1) - 1) := Nat.mul_le_mul_left _ (by omega)
  · rw [sigma1_euclid hq]
    set B := 2 ^ (k + 1) - 1 with hB
    have hBv : 2 * 2 ^ k = B + 1 := by omega
    have e1 : 2 * (2 ^ k * B) = (B + 1) * B := by rw [← Nat.mul_assoc, hBv]
    have e2 : B * (1 + B) = (B + 1) * B := by ring
    omega

/-- The hypothesis that there are infinitely many Mersenne primes. -/
def InfinitelyManyMersennePrimes : Prop :=
  ∀ N : ℕ, ∃ k : ℕ, N < k ∧ (2 ^ (k + 1) - 1).Prime

/-- **Hyperperfect Infinitude, Mersenne route.**  If there are infinitely many Mersenne
primes then there are infinitely many (even perfect, hence `1`-hyperperfect) numbers. -/
theorem hyperperfectInfinitude_of_mersenne (H : InfinitelyManyMersennePrimes) :
    hyperperfectSet.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨k, hNk, hq⟩ := H N
  refine ⟨2 ^ k * (2 ^ (k + 1) - 1), ⟨1, isHyperperfectWith_one_euclid (by omega) hq⟩, ?_⟩
  have h4 : 4 ≤ 2 ^ (k + 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
  calc N < k := hNk
  _ < 2 ^ k := hk2
  _ = 2 ^ k * 1 := by ring
  _ ≤ 2 ^ k * (2 ^ (k + 1) - 1) := Nat.mul_le_mul_left _ (by omega)

/-! ## Sanity checks: concrete hyperperfect numbers -/

example : IsHyperperfectWith 1 6 := ⟨by norm_num, by norm_num, by decide⟩

example : IsHyperperfectWith 2 21 := ⟨by norm_num, by norm_num, by decide⟩

example : IsHyperperfectWith 6 301 := ⟨by norm_num, by norm_num, by decide⟩

example : IsHyperperfect (7 * brockPartner 7) := by
  have h : brockPartner 7 = 43 := by norm_num [brockPartner]
  exact isHyperperfect_brock (by norm_num) (by rw [h]; norm_num)

end Brockian.HyperperfectNumbers

