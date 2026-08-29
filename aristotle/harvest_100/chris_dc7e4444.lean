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

/-- `sigma n` is the sum of all divisors of `n`. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is `k`-hyperperfect when `k ≥ 1`, `n > 1` and `n = 1 + k * (σ(n) - n - 1)`,
i.e. `n` is one more than `k` times the sum of its nontrivial divisors.
The equation is written in subtraction-free form to avoid truncated natural subtraction. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ 1 < n ∧ n + k * (n + 1) = 1 + k * sigma n

/-- The set of hyperperfect numbers. -/
def Hyperperfect : Set ℕ := {n | ∃ k, IsHyperperfect k n}

lemma sigma_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigma (a * b) = sigma a * sigma b :=
  Nat.Coprime.sum_divisors_mul h

lemma sigma_prime {p : ℕ} (hp : p.Prime) : sigma p = p + 1 :=
  Nat.Prime.sum_divisors hp

/-- The hyperperfect equation in the familiar subtracted form. -/
lemma isHyperperfect_iff {k n : ℕ} (hk : 0 < k) (hn : 1 < n) :
    IsHyperperfect k n ↔ n = 1 + k * (sigma n - n - 1) := by
  have hd : n + 1 ≤ sigma n := by
    have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.2 (by omega)
    have hn' : n ∈ n.divisors := Nat.mem_divisors_self n (by omega)
    have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have := Finset.sum_le_sum_of_subset hsub (f := fun d => d)
    rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ n)] at this
    simpa [sigma, Nat.add_comm] using this
  obtain ⟨s, hs⟩ : ∃ s, sigma n = n + 1 + s := ⟨sigma n - (n + 1), by omega⟩
  have hsub : n + 1 + s - n - 1 = s := by omega
  simp only [IsHyperperfect, hs, hsub, Nat.mul_add]
  constructor
  · rintro ⟨-, -, h⟩
    omega
  · intro h
    exact ⟨hk, hn, by omega⟩

/-! ## Perfect numbers are `1`-hyperperfect -/

lemma isHyperperfect_one_of_perfect {n : ℕ} (hn : Nat.Perfect n) (h1 : 1 < n) :
    IsHyperperfect 1 n := by
  have h : sigma n = 2 * n := by
    have := (Nat.perfect_iff_sum_divisors_eq_two_mul (by omega)).1 hn
    simpa [sigma] using this
  exact ⟨one_pos, h1, by omega⟩

/-! ## The `p, p² - p + 1` family

If `p` and `q = p² - p + 1` are both prime, then `p * q` is `(p-1)`-hyperperfect.
For `p = 2, 3, 7, 43, ...` this gives `6, 21, 301, ...`. -/

lemma isHyperperfect_of_prime_pair {p q k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : q + p = p * p + 1) (hk : k + 1 = p) : IsHyperperfect k (p * q) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hk0 : 0 < k := by omega
  have hqval : q = k * k + k + 1 := by
    subst hk; nlinarith [hpq]
  have hpne : p ≠ q := by
    intro h
    subst h
    nlinarith
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpne
  have hs : sigma (p * q) = (p + 1) * (q + 1) := by
    rw [sigma_mul_of_coprime hcop, sigma_prime hp, sigma_prime hq]
  refine ⟨hk0, ?_, ?_⟩
  · have : 2 ≤ q := hq.two_le
    nlinarith
  · rw [hs, hqval, ← hk]
    ring

/-- `6` is `1`-hyperperfect (it is perfect). -/
theorem isHyperperfect_one_six : IsHyperperfect 1 6 := by
  refine isHyperperfect_of_prime_pair (p := 2) (q := 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `21` is `2`-hyperperfect. -/
theorem isHyperperfect_two_21 : IsHyperperfect 2 21 := by
  refine isHyperperfect_of_prime_pair (p := 3) (q := 7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `301 = 7 * 43` is `6`-hyperperfect. -/
theorem isHyperperfect_six_301 : IsHyperperfect 6 301 := by
  refine isHyperperfect_of_prime_pair (p := 7) (q := 43) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ## A divisibility characterization, and the first few hyperperfect numbers -/

/-- For `n > 1`, `n` is hyperperfect exactly when the sum `s` of its nontrivial divisors
(the divisors other than `1` and `n`) is positive and divides `n - 1`. -/
theorem mem_hyperperfect_iff {n : ℕ} (hn : 1 < n) :
    n ∈ Hyperperfect ↔ 0 < sigma n - n - 1 ∧ (sigma n - n - 1) ∣ (n - 1) := by
  constructor
  · rintro ⟨k, hk, -, heq⟩
    have hk' := (isHyperperfect_iff hk hn).1 ⟨hk, hn, heq⟩
    refine ⟨?_, ⟨k, by rw [Nat.mul_comm]; omega⟩⟩
    rcases Nat.eq_zero_or_pos (sigma n - n - 1) with h | h
    · rw [h, Nat.mul_zero] at hk'; omega
    · exact h
  · rintro ⟨hs, c, hc⟩
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · simp at hc; omega
      · exact h
    exact ⟨c, (isHyperperfect_iff hc0 hn).2 (by rw [Nat.mul_comm]; omega)⟩

set_option maxRecDepth 10000 in
/-- The hyperperfect numbers below `800` are `6, 21, 28, 301, 325, 496, 697`; here we check
that each of them is indeed hyperperfect. -/
theorem hyperperfect_examples :
    ({6, 21, 28, 301, 325, 496, 697} : Set ℕ) ⊆ Hyperperfect := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, isHyperperfect_one_six⟩
  · exact ⟨2, isHyperperfect_two_21⟩
  · exact ⟨1, by norm_num, by norm_num, by decide⟩
  · exact ⟨6, isHyperperfect_six_301⟩
  · exact ⟨3, by norm_num, by norm_num, by decide⟩
  · exact ⟨1, by norm_num, by norm_num, by decide⟩
  · exact ⟨12, by norm_num, by norm_num, by decide⟩

/-! ## The main conditional reduction -/

/-- **Hyperperfect Infinitude (conditional).**
If there are infinitely many primes `p` for which `p² - p + 1` is also prime, then there
are infinitely many hyperperfect numbers.  (Unconditional infinitude of hyperperfect
numbers is an open problem; already the case `k = 1`, i.e. perfect numbers, is open.) -/
theorem HyperperfectInfinitude
    (H : {p : ℕ | p.Prime ∧ (p * p - p + 1).Prime}.Infinite) : Hyperperfect.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  obtain ⟨p, ⟨hp, hq⟩, hpN⟩ := H.exists_gt N
  have hp2 : 2 ≤ p := hp.two_le
  set q := p * p - p + 1 with hqdef
  have hpq : q + p = p * p + 1 := by
    have : p ≤ p * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  refine ⟨p * q, ⟨p - 1, isHyperperfect_of_prime_pair hp hq hpq (by omega)⟩, ?_⟩
  have hq1 : 1 ≤ q := by omega
  calc N < p := hpN
    _ ≤ p * q := Nat.le_mul_of_pos_right p (by omega)

/-! ## A second conditional reduction: via Mersenne primes -/

lemma sigma_two_pow (k : ℕ) : sigma (2 ^ k) + 1 = 2 ^ (k + 1) := by
  have h : sigma (2 ^ k) = ∑ i ∈ Finset.range (k + 1), 2 ^ i := by
    simpa [sigma] using
      (Nat.sum_divisors_prime_pow (p := 2) (k := k) (f := fun d => d) Nat.prime_two)
  rw [h]
  clear h
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      rw [pow_succ] at ih ⊢
      omega

/-- If `q = 2 ^ (k+1) - 1` is prime, then the even perfect number `2 ^ k * q` is
`1`-hyperperfect. -/
lemma isHyperperfect_one_two_pow_mul_mersenne {k q : ℕ} (hq : q.Prime) (hqk : q + 1 = 2 ^ (k + 1))
    (hk : 1 ≤ k) : IsHyperperfect 1 (2 ^ k * q) := by
  have hcop : Nat.Coprime (2 ^ k) q := by
    have hq2 : q ≠ 2 := by
      rintro rfl
      have : (2 : ℕ) ^ (k + 1) = 3 := by omega
      have h4 : (4 : ℕ) ≤ 2 ^ (k + 1) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
  have hs : sigma (2 ^ k * q) = (2 ^ (k + 1) - 1) * (q + 1) := by
    have h2 : sigma (2 ^ k) = 2 ^ (k + 1) - 1 := by have := sigma_two_pow k; omega
    rw [sigma_mul_of_coprime hcop, sigma_prime hq, h2]
  have hq3 : 3 ≤ q := by
    have h4 : (4 : ℕ) ≤ 2 ^ (k + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2k : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hqq : (2 : ℕ) ^ (k + 1) - 1 = q := by omega
  rw [hqq] at hs
  refine ⟨one_pos, ?_, ?_⟩
  · nlinarith
  · rw [hs]
    have : 2 ^ k * 2 = 2 ^ (k + 1) := by rw [pow_succ]
    nlinarith [hqk]

/-- **Hyperperfect Infinitude (conditional, Mersenne version).**
If there are infinitely many Mersenne primes, then there are infinitely many hyperperfect
numbers (indeed infinitely many `1`-hyperperfect, i.e. perfect, numbers). -/
theorem hyperperfect_infinite_of_infinitely_many_mersenne_primes
    (H : ∀ N : ℕ, ∃ k, N < k ∧ (2 ^ (k + 1) - 1).Prime) : Hyperperfect.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  obtain ⟨k, hkN, hq⟩ := H N
  set q := 2 ^ (k + 1) - 1 with hqdef
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hqk : q + 1 = 2 ^ (k + 1) := by omega
  have hk1 : 1 ≤ k := by omega
  refine ⟨2 ^ k * q, ⟨1, isHyperperfect_one_two_pow_mul_mersenne hq hqk hk1⟩, ?_⟩
  have hq3 : 3 ≤ q := by
    have h4 : (4 : ℕ) ≤ 2 ^ (k + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hkk : k < 2 ^ k := Nat.lt_two_pow_self
  calc N < k := hkN
    _ < 2 ^ k := hkk
    _ ≤ 2 ^ k * q := Nat.le_mul_of_pos_right _ (by omega)

end Brockian.HyperperfectNumbers

