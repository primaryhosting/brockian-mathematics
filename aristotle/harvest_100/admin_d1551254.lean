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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `IsKHyperperfect k n` states that `n` is a `k`-hyperperfect number, i.e. `k > 0`, `n > 1` and
`n = 1 + k * (σ n - n - 1)`, written here in the subtraction-free form
`k * σ n + 1 = (k + 1) * n + k`. -/
def IsKHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ 1 < n ∧ k * ArithmeticFunction.sigma 1 n + 1 = (k + 1) * n + k

/-- A hyperperfect number is a number that is `k`-hyperperfect for some `k ≥ 1`.
The `1`-hyperperfect numbers are exactly the perfect numbers. -/
def IsHyperperfect (n : ℕ) : Prop := ∃ k, IsKHyperperfect k n

/-- The divisor-sum of a prime. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  simp [ArithmeticFunction.sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne,
    Nat.add_comm]

/-- The divisor-sum of a prime power is the corresponding geometric sum. -/
lemma sigma_one_prime_pow {q : ℕ} (hq : q.Prime) (j : ℕ) :
    ArithmeticFunction.sigma 1 (q ^ j) = ∑ i ∈ range (j + 1), q ^ i := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hq]

/-- Geometric summation formula, in subtraction-free form. -/
lemma geom_sum_succ (k j : ℕ) :
    k * (∑ i ∈ range (j + 1), (k + 1) ^ i) + 1 = (k + 1) ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, pow_succ ((k + 1)) (j + 1)]
      rw [← ih]
      ring

/-- **Construction of hyperperfect numbers.** If `q = k + 1` is prime and `p = q ^ (j+1) - k`
is prime (with `j ≥ 1`), then `q ^ j * p` is a `k`-hyperperfect number.

For `k = 1` this is the Euclid construction of even perfect numbers from Mersenne primes;
for `k = 2` it is the family `3 ^ j * (3 ^ (j+1) - 2)` (e.g. `21`, `2133`, ...). -/
theorem isKHyperperfect_pow_mul_prime {k j p : ℕ} (hk : 0 < k) (hq : Nat.Prime (k + 1))
    (hj : 0 < j) (hp : p.Prime) (hpk : p + k = (k + 1) ^ (j + 1)) :
    IsKHyperperfect k ((k + 1) ^ j * p) := by
  -- `p` is strictly larger than `k + 1`
  have hlt : k + 1 < p := by
    have h2 : (k + 1) ^ 2 ≤ (k + 1) ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hsq : (k + 1) ^ 2 = k * k + 2 * k + 1 := by ring
    nlinarith [hpk, h2]
  have hne : k + 1 ≠ p := by omega
  have hcop : Nat.Coprime ((k + 1) ^ j) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hq hp).mpr hne)
  refine ⟨hk, ?_, ?_⟩
  · have h1 : 1 < p := hp.one_lt
    have hone : 1 ≤ (k + 1) ^ j := Nat.one_le_pow _ _ (by omega)
    calc 1 < p := h1
      _ = 1 * p := (one_mul p).symm
      _ ≤ (k + 1) ^ j * p := Nat.mul_le_mul_right _ hone
  · -- compute the divisor sum
    set S := ∑ i ∈ range (j + 1), (k + 1) ^ i with hS
    have hsig : ArithmeticFunction.sigma 1 ((k + 1) ^ j * p) = S * (p + 1) := by
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        sigma_one_prime_pow hq, sigma_one_prime hp, ← hS]
    have hA : k * S + 1 = p + k := by rw [hS, geom_sum_succ, ← hpk]
    have hpow : (k + 1) * ((k + 1) ^ j * p) = (p + k) * p := by
      rw [← Nat.mul_assoc, ← pow_succ' (k + 1) j, ← hpk]
    rw [hsig, hpow]
    calc k * (S * (p + 1)) + 1 = (k * S) * p + (k * S + 1) := by ring
      _ = (k * S) * p + (p + k) := by rw [hA]
      _ = (k * S + 1) * p + k := by ring
      _ = (p + k) * p + k := by rw [hA]

/-- Any `k`-hyperperfect number is hyperperfect. -/
lemma isHyperperfect_of_isKHyperperfect {k n : ℕ} (h : IsKHyperperfect k n) :
    IsHyperperfect n := ⟨k, h⟩

/-- `6` is a (`1`-)hyperperfect number. -/
theorem isHyperperfect_six : IsHyperperfect 6 :=
  ⟨1, by refine ⟨one_pos, by norm_num, ?_⟩; decide⟩

/-- `21` is a `2`-hyperperfect number. -/
theorem isHyperperfect_twentyone : IsHyperperfect 21 :=
  ⟨2, by refine ⟨two_pos, by norm_num, ?_⟩; decide⟩

/-- `28` is a (`1`-)hyperperfect number. -/
theorem isHyperperfect_twentyeight : IsHyperperfect 28 :=
  ⟨1, by refine ⟨one_pos, by norm_num, ?_⟩; decide⟩

/-- `301` is a `6`-hyperperfect number. -/
theorem isHyperperfect_threehundredone : IsHyperperfect 301 :=
  ⟨6, by refine ⟨by norm_num, by norm_num, ?_⟩; decide⟩

/-- **Hyperperfect Infinitude (conditional reduction).**

Assume the (open) hypothesis `H`: for every bound `N` there is some `k > N` such that `k + 1`
is prime and `(k + 1) ^ (j + 1) - k` is prime for some `j ≥ 1`.  Then there are infinitely many
hyperperfect numbers.

The hypothesis is stated in subtraction-free form: `p + k = (k + 1) ^ (j + 1)` with `p` prime.
It holds e.g. for `j = 1` whenever `q = k + 1` and `q ^ 2 - q + 1` are both prime
(`q = 2, 3, 7, 13, ...` giving the hyperperfect numbers `6, 21, 301, 2041, ...`). -/
theorem HyperperfectInfinitude
    (H : ∀ N : ℕ, ∃ k j p : ℕ, N < k ∧ Nat.Prime (k + 1) ∧ 0 < j ∧ Nat.Prime p ∧
      p + k = (k + 1) ^ (j + 1)) :
    {n : ℕ | IsHyperperfect n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨k, j, p, hNk, hq, hj, hp, hpk⟩ := H N
  refine ⟨(k + 1) ^ j * p, ?_, ?_⟩
  · exact isHyperperfect_of_isKHyperperfect
      (isKHyperperfect_pow_mul_prime (by omega) hq hj hp hpk)
  · -- `p` alone already exceeds `N`
    have h2 : (k + 1) ^ 2 ≤ (k + 1) ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hsq : (k + 1) ^ 2 = k * k + 2 * k + 1 := by ring
    have hpN : N < p := by nlinarith [hpk, h2]
    have hone : 1 ≤ (k + 1) ^ j := Nat.one_le_pow _ _ (by omega)
    calc N < p := hpN
      _ = 1 * p := (one_mul p).symm
      _ ≤ (k + 1) ^ j * p := Nat.mul_le_mul_right _ hone

/-- **Conditional infinitude of `2`-hyperperfect numbers.**  If there are infinitely many `j`
with `3 ^ (j + 1) - 2` prime, then there are infinitely many `2`-hyperperfect numbers. -/
theorem twoHyperperfectInfinitude
    (H : ∀ N : ℕ, ∃ j p : ℕ, N < j ∧ Nat.Prime p ∧ p + 2 = 3 ^ (j + 1)) :
    {n : ℕ | IsKHyperperfect 2 n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨j, p, hNj, hp, hpj⟩ := H N
  refine ⟨3 ^ j * p, ?_, ?_⟩
  · have := isKHyperperfect_pow_mul_prime (k := 2) (j := j) (p := p) two_pos (by norm_num)
      (by omega) hp (by simpa using hpj)
    simpa using this
  · have hj : N < 3 ^ j := lt_of_lt_of_le hNj (Nat.lt_pow_self (by norm_num)).le
    have h1 : 1 ≤ p := hp.one_lt.le.trans' (by norm_num)
    calc N < 3 ^ j := hj
      _ = 3 ^ j * 1 := (mul_one _).symm
      _ ≤ 3 ^ j * p := Nat.mul_le_mul_left _ h1

end Brockian.HyperperfectNumbers

