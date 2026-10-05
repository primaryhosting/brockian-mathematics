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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

/-- `sigmaOne n` is the sum of all divisors of `n`, usually written `σ₁ (n)`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is **`k`-hyperperfect** when `n = 1 + k * (σ₁ (n) - n - 1)`, i.e. when `n` is one more
than `k` times the sum of its nontrivial proper divisors.  Here the defining identity is written
in the subtraction-free form `k * σ₁ (n) + 1 = (k + 1) * n + k`.  For `k = 1` this is exactly the
notion of a perfect number. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  1 < n ∧ k * sigmaOne n + 1 = (k + 1) * n + k

/-- The Brockian conjecture on hyperperfect numbers: for every `k ≥ 1` there exists a
`k`-hyperperfect number.  This statement is open; the results below establish it under an
explicit primality hypothesis and reduce it to a purely prime-theoretic statement. -/
def HyperperfectAllKConjecture : Prop :=
  ∀ k : ℕ, 0 < k → ∃ n : ℕ, IsHyperperfect k n

/-! ## Basic facts about `sigmaOne` -/

theorem sigmaOne_prime {p : ℕ} (hp : p.Prime) : sigmaOne p = 1 + p := by
  simp [sigmaOne, hp.divisors, Finset.sum_pair hp.one_lt.ne]

theorem sigmaOne_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigmaOne (m * n) = sigmaOne m * sigmaOne n := h.sum_divisors_mul

theorem sigmaOne_eq_properDivisors_add (n : ℕ) :
    sigmaOne n = (∑ d ∈ n.properDivisors, d) + n := by
  rw [sigmaOne, ← Nat.sum_divisors_eq_sum_properDivisors_add_self]

/-! ## Reformulations -/

/-- Reformulation of `k`-hyperperfection in terms of the sum `s (n)` of the *proper* divisors of
`n`: the condition is `n = 1 + k * (s (n) - 1)`, written subtraction-free. -/
theorem isHyperperfect_iff_properDivisors (k n : ℕ) :
    IsHyperperfect k n ↔ 1 < n ∧ k * (∑ d ∈ n.properDivisors, d) + 1 = n + k := by
  rw [IsHyperperfect, sigmaOne_eq_properDivisors_add]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by nlinarith⟩

/-- For `k = 1` hyperperfection is exactly perfection. -/
theorem isHyperperfect_one_iff_perfect (n : ℕ) : IsHyperperfect 1 n ↔ n.Perfect ∧ 1 < n := by
  rw [isHyperperfect_iff_properDivisors, Nat.Perfect]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, by omega⟩, h1⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    omega

/-- The algebraic heart of the two-prime case: with `p = k + a` and `q = k + b`, the
hyperperfection identity for `p * q` is equivalent to `a * b = k ^ 2 + 1`. -/
theorem mul_sub_eq_iff (k a b : ℕ) :
    k * ((1 + (k + a)) * (1 + (k + b))) + 1 = (k + 1) * ((k + a) * (k + b)) + k ↔
      a * b = k ^ 2 + 1 := by
  constructor <;> intro h <;> nlinarith [h]

/-- Structure of hyperperfect numbers that are products of two distinct primes: `p * q` is
`k`-hyperperfect exactly when `(p - k) * (q - k) = k ^ 2 + 1`, both `p` and `q` exceeding `k`. -/
theorem isHyperperfect_prime_mul_prime_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    IsHyperperfect k (p * q) ↔ k < p ∧ k < q ∧ (p - k) * (q - k) = k ^ 2 + 1 := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hs : sigmaOne (p * q) = (1 + p) * (1 + q) := by
    rw [sigmaOne_mul_of_coprime hcop, sigmaOne_prime hp, sigmaOne_prime hq]
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have h1 : 1 < p * q := by nlinarith
  rw [IsHyperperfect, hs]
  constructor
  · rintro ⟨-, h⟩
    have hkp : k < p := by
      by_contra hc
      push_neg at hc
      nlinarith
    have hkq : k < q := by
      by_contra hc
      push_neg at hc
      nlinarith
    refine ⟨hkp, hkq, ?_⟩
    have e1 : p = k + (p - k) := by omega
    have e2 : q = k + (q - k) := by omega
    rw [e1, e2] at h
    exact (mul_sub_eq_iff k (p - k) (q - k)).1 h
  · rintro ⟨hkp, hkq, h⟩
    refine ⟨h1, ?_⟩
    have e1 : p = k + (p - k) := by omega
    have e2 : q = k + (q - k) := by omega
    rw [e1, e2]
    exact (mul_sub_eq_iff k (p - k) (q - k)).2 h

/-- Whenever `k ^ 2 + 1 = a * b` with `k + a` and `k + b` distinct primes, the number
`(k + a) * (k + b)` is `k`-hyperperfect. -/
theorem isHyperperfect_of_factorization {k a b : ℕ} (hab : a * b = k ^ 2 + 1)
    (ha : Nat.Prime (k + a)) (hb : Nat.Prime (k + b)) (hne : k + a ≠ k + b) :
    IsHyperperfect k ((k + a) * (k + b)) := by
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · simp [h] at hab
    · exact h
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · simp [h] at hab
    · exact h
  rw [isHyperperfect_prime_mul_prime_iff ha hb hne]
  refine ⟨by omega, by omega, ?_⟩
  simpa using hab

/-- If `k + 1` and `k ^ 2 + k + 1` are both prime, then `(k + 1) * (k ^ 2 + k + 1)` is a
`k`-hyperperfect number. -/
theorem isHyperperfect_of_primes {k : ℕ} (hk : 0 < k) (hp : Nat.Prime (k + 1))
    (hq : Nat.Prime (k ^ 2 + k + 1)) :
    IsHyperperfect k ((k + 1) * (k ^ 2 + k + 1)) := by
  have e : k ^ 2 + k + 1 = k + (k ^ 2 + 1) := by ring
  have hne : k + 1 ≠ k + (k ^ 2 + 1) := by
    have : 0 < k ^ 2 := by positivity
    omega
  have h := isHyperperfect_of_factorization (k := k) (a := 1) (b := k ^ 2 + 1)
    (by ring) (by simpa using hp) (by rw [← e]; exact hq) hne
  simpa [← e] using h

/-! ## Main statement -/

/-- **Main theorem (partial and conditional forms of "hyperperfect numbers exist for all `k`").**

The Brockian conjecture `HyperperfectAllKConjecture` asserts that a `k`-hyperperfect number exists
for every `k ≥ 1`; it is open.  This theorem records what can be proved unconditionally:

* for every `k ≥ 1` for which `k + 1` and `k ^ 2 + k + 1` are both prime, the number
  `(k + 1) * (k ^ 2 + k + 1)` is `k`-hyperperfect (so such `k` are settled);
* conversely, the whole conjecture follows from the purely prime-theoretic statement that for
  every `k ≥ 1` the number `k ^ 2 + 1` admits a factorization `a * b` with `k + a` and `k + b`
  distinct primes;
* and this prime-theoretic statement is not merely sufficient but *necessary* for the
  two-prime (semiprime) witnesses: a product of two distinct primes `p * q` is `k`-hyperperfect
  if and only if `k < p`, `k < q` and `(p - k) * (q - k) = k ^ 2 + 1`. -/
theorem HyperperfectAllK :
    (∀ k : ℕ, 0 < k → Nat.Prime (k + 1) → Nat.Prime (k ^ 2 + k + 1) →
        IsHyperperfect k ((k + 1) * (k ^ 2 + k + 1))) ∧
    ((∀ k : ℕ, 0 < k → ∃ a b : ℕ, a * b = k ^ 2 + 1 ∧ Nat.Prime (k + a) ∧ Nat.Prime (k + b) ∧
        k + a ≠ k + b) → HyperperfectAllKConjecture) ∧
    (∀ k p q : ℕ, p.Prime → q.Prime → p ≠ q →
        (IsHyperperfect k (p * q) ↔ k < p ∧ k < q ∧ (p - k) * (q - k) = k ^ 2 + 1)) := by
  refine ⟨fun k hk hp hq => isHyperperfect_of_primes hk hp hq, ?_, ?_⟩
  · intro H k hk
    obtain ⟨a, b, hab, ha, hb, hne⟩ := H k hk
    exact ⟨_, isHyperperfect_of_factorization hab ha hb hne⟩
  · intro k p q hp hq hpq
    exact isHyperperfect_prime_mul_prime_iff hp hq hpq

/-! ## Non-vacuity: concrete hyperperfect numbers -/

theorem isHyperperfect_one_six : IsHyperperfect 1 6 := by
  have h : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h, isHyperperfect_prime_mul_prime_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem isHyperperfect_two_21 : IsHyperperfect 2 21 := by
  have h : (21 : ℕ) = 3 * 7 := by norm_num
  rw [h, isHyperperfect_prime_mul_prime_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem isHyperperfect_six_301 : IsHyperperfect 6 301 := by
  have h : (301 : ℕ) = 7 * 43 := by norm_num
  rw [h, isHyperperfect_prime_mul_prime_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem isHyperperfect_twelve_697 : IsHyperperfect 12 697 := by
  have h : (697 : ℕ) = 17 * 41 := by norm_num
  rw [h, isHyperperfect_prime_mul_prime_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end Brockian.HyperperfectNumbers

