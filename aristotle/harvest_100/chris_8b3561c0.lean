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

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigmaOne n` is the sum of all divisors of `n`, usually written `σ₁ (n)`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is **`k`-hyperperfect** if `n = 1 + k * (σ₁(n) - n - 1)`, i.e. `n` is one more than
`k` times the sum of the divisors of `n` other than `1` and `n`.  The defining equation is
stated in subtraction-free form: `n + k * (n + 1) = 1 + k * σ₁(n)`. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ 1 < n ∧ n + k * (n + 1) = 1 + k * sigmaOne n

/-- The set of hyperperfect numbers (hyperperfect for some order `k ≥ 1`). -/
def Hyperperfect : Set ℕ := {n | ∃ k, IsHyperperfect k n}

/-- The primes `p` for which `p² - p + 1` is again prime.  For each such `p` the number
`p * (p² - p + 1)` is `(p-1)`-hyperperfect (see `isHyperperfect_mul_of_prime_pair`). -/
def BrockPrimes : Set ℕ := {p | p.Prime ∧ (p * p - p + 1).Prime}

/-- The sum of divisors of a product of two distinct primes. -/
lemma sigmaOne_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    sigmaOne (p * q) = (p + 1) * (q + 1) := by
  unfold sigmaOne
  rw [Nat.Coprime.sum_divisors_mul ((Nat.coprime_primes hp hq).2 hpq), hp.sum_divisors,
    hq.sum_divisors]

/-- **Key lemma** (Minoli's family, case of exponent two).  If `p` and `q = p² - p + 1` are both
prime, then `n = p * q` is `(p-1)`-hyperperfect. -/
lemma isHyperperfect_mul_of_prime_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqe : q + p = p * p + 1) : IsHyperperfect (p - 1) (p * q) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  have hk : 1 ≤ k := by have := hp.two_le; omega
  have hexp : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
  have hq' : q = k * k + k + 1 := by linarith
  subst hq'
  have hkk : 1 ≤ k * k := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hpq : k + 1 ≠ k * k + k + 1 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · have : 2 ≤ k + 1 := by omega
    calc 1 < 2 * 1 := by omega
      _ ≤ (k + 1) * (k * k + k + 1) := Nat.mul_le_mul this (by omega)
  · rw [Nat.add_sub_cancel, sigmaOne_mul_of_primes hp hq hpq]
    ring

/-- `21 = 3 * 7` is `2`-hyperperfect. -/
lemma isHyperperfect_two_21 : IsHyperperfect 2 21 := by
  have := isHyperperfect_mul_of_prime_pair (p := 3) (q := 7)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `301 = 7 * 43` is `6`-hyperperfect. -/
lemma isHyperperfect_six_301 : IsHyperperfect 6 301 := by
  have := isHyperperfect_mul_of_prime_pair (p := 7) (q := 43)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `2041 = 13 * 157` is `12`-hyperperfect. -/
lemma isHyperperfect_twelve_2041 : IsHyperperfect 12 2041 := by
  have := isHyperperfect_mul_of_prime_pair (p := 13) (q := 157)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- The hypothesis of `HyperperfectInfinitude` is not vacuous: `3`, `7` and `13` all belong to
`BrockPrimes`. -/
lemma mem_brockPrimes : (3 : ℕ) ∈ BrockPrimes ∧ (7 : ℕ) ∈ BrockPrimes ∧ (13 : ℕ) ∈ BrockPrimes := by
  refine ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩ <;> norm_num

/-! ### A second reduction: Mersenne primes

Every (even) perfect number is `1`-hyperperfect, so Euclid's construction gives a second
conditional route to infinitude. -/

lemma sum_range_two_pow_succ (k : ℕ) : (∑ x ∈ Finset.range (k + 1), 2 ^ x) + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      omega

/-- The sum of the divisors of `2 ^ k`. -/
lemma sigmaOne_two_pow (k : ℕ) : sigmaOne (2 ^ k) + 1 = 2 ^ (k + 1) := by
  unfold sigmaOne
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  exact sum_range_two_pow_succ k

/-- **Euclid's construction, hyperperfect form.**  If `q = 2 ^ (k+1) - 1` is prime (`k ≥ 1`), then
the perfect number `2 ^ k * q` is `1`-hyperperfect. -/
lemma isHyperperfect_one_of_mersenne {k q : ℕ} (hk : 1 ≤ k) (hq : q.Prime)
    (hqe : q + 1 = 2 ^ (k + 1)) : IsHyperperfect 1 (2 ^ k * q) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hqodd : q ≠ 2 := by
    intro h
    rw [h] at hqe
    have : 2 ^ (1 + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcop : Nat.Coprime (2 ^ k) q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hq).2 (fun h => hqodd h.symm))
  have hsig : sigmaOne (2 ^ k * q) = q * (q + 1) := by
    unfold sigmaOne
    rw [Nat.Coprime.sum_divisors_mul hcop, hq.sum_divisors]
    have h1 := sigmaOne_two_pow k
    unfold sigmaOne at h1
    have h2 : (∑ d ∈ (2 ^ k).divisors, d) = q := by omega
    rw [h2]
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  refine ⟨by norm_num, ?_, ?_⟩
  · have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    calc 1 < 2 * 2 := by norm_num
      _ ≤ 2 ^ k * q := Nat.mul_le_mul (by omega) hq2
  · have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have key : q * (q + 1) = 2 * (2 ^ k * q) := by rw [hqe, hpow]; ring
    rw [hsig, key]
    ring

/-- **Conditional infinitude of hyperperfect numbers, via Mersenne primes.**  If there are
infinitely many Mersenne primes, then there are infinitely many hyperperfect numbers (indeed
infinitely many `1`-hyperperfect, i.e. perfect, numbers). -/
theorem hyperperfectInfinitude_of_infinite_mersennePrimes
    (H : {p : ℕ | (2 ^ p - 1).Prime}.Infinite) : Hyperperfect.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hp, hpN⟩ := H.exists_gt (N + 2)
  simp only [Set.mem_setOf_eq] at hp
  have hp2 : 2 ≤ p := by
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at hp
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have hone : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hqe : (2 ^ (k + 1) - 1) + 1 = 2 ^ (k + 1) := by omega
  refine ⟨2 ^ k * (2 ^ (k + 1) - 1), ⟨1, isHyperperfect_one_of_mersenne (by omega) hp hqe⟩, ?_⟩
  have hq2 : 2 ≤ 2 ^ (k + 1) - 1 := hp.two_le
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  calc N < k := by omega
    _ < 2 ^ k := hlt
    _ = 2 ^ k * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ k * (2 ^ (k + 1) - 1) := Nat.mul_le_mul_left _ (by omega)

/-- **Conditional infinitude of hyperperfect numbers.**  If there are infinitely many primes `p`
for which `p² - p + 1` is also prime, then there are infinitely many hyperperfect numbers. -/
theorem HyperperfectInfinitude (H : BrockPrimes.Infinite) : Hyperperfect.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, ⟨hp, hq⟩, hpN⟩ := H.exists_gt N
  have hp2 : 2 ≤ p := hp.two_le
  have hple : p ≤ p * p := Nat.le_mul_of_pos_left p (by omega)
  have hqe : (p * p - p + 1) + p = p * p + 1 := by omega
  refine ⟨p * (p * p - p + 1), ⟨p - 1, isHyperperfect_mul_of_prime_pair hp hq hqe⟩, ?_⟩
  have h1 : 1 ≤ p * p - p + 1 := by omega
  calc N < p := hpN
    _ = p * 1 := (Nat.mul_one p).symm
    _ ≤ p * (p * p - p + 1) := Nat.mul_le_mul_left p h1

end Brockian.HyperperfectNumbers

