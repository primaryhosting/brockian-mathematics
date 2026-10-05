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

/-- `sigmaOne n` is the sum of the divisors of `n`. -/
def sigmaOne (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

lemma sigmaOne_eq_sum (n : ℕ) : sigmaOne n = ∑ d ∈ n.divisors, d := by
  simp [sigmaOne, ArithmeticFunction.sigma_apply]

/-- A natural number `n` is **hyperperfect** if there is a positive integer `k` with
`n = 1 + k * (σ(n) - n - 1)`, where `σ` is the sum-of-divisors function.  (For `k = 1`
this is exactly the condition that `n` is a perfect number.)  The subtraction is
performed in `ℤ`, so no truncation occurs. -/
def Hyperperfect (n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (n : ℤ) = 1 + (k : ℤ) * ((sigmaOne n : ℤ) - (n : ℤ) - 1)

/-- `n` is `k`-hyperperfect. -/
def KHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ (n : ℤ) = 1 + (k : ℤ) * ((sigmaOne n : ℤ) - (n : ℤ) - 1)

lemma hyperperfect_of_kHyperperfect {k n : ℕ} (h : KHyperperfect k n) : Hyperperfect n :=
  ⟨k, h.1, h.2⟩

/-! ## Sum of divisors of a product of two distinct primes -/

lemma sigmaOne_prime {p : ℕ} (hp : p.Prime) : sigmaOne p = p + 1 := by
  simp [sigmaOne, ArithmeticFunction.sigma_apply, hp.sum_divisors]

lemma sigmaOne_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    sigmaOne (p * q) = (p + 1) * (q + 1) := by
  rw [sigmaOne,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      ((Nat.coprime_primes hp hq).2 hne)]
  simp [ArithmeticFunction.sigma_apply, hp.sum_divisors, hq.sum_divisors]

/-! ## The basic infinite family

If `p` and `q = p² - p + 1` are both prime, then `n = p * q` is `(p-1)`-hyperperfect:
indeed `σ(n) - n - 1 = p + q = p² + 1` while `n - 1 = p³ - p² + p - 1 = (p-1)(p² + 1)`.
-/

lemma kHyperperfect_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : q + p = p * p + 1) : KHyperperfect (p - 1) (p * q) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hlt : p < q := by nlinarith
  have hne : p ≠ q := Nat.ne_of_lt hlt
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have h1 : (1 : ℕ) ≤ p := le_trans (by norm_num) hp2
    push_cast [h1]
    ring
  have hq' : (q : ℤ) + (p : ℤ) = (p : ℤ) * (p : ℤ) + 1 := by exact_mod_cast hpq
  refine ⟨by omega, ?_⟩
  rw [sigmaOne_mul_primes hp hq hne, hcast]
  push_cast
  nlinarith [hq']

lemma hyperperfect_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : q + p = p * p + 1) : Hyperperfect (p * q) :=
  hyperperfect_of_kHyperperfect (kHyperperfect_mul_of_primes hp hq hpq)

/-! ## A decidable criterion -/

lemma sigmaOne_zero : sigmaOne 0 = 0 := by decide

lemma sigmaOne_one : sigmaOne 1 = 1 := by decide

/-- For `n` with `σ(n) > n + 1` (i.e. `n` composite), hyperperfection is equivalent to the
purely arithmetic, decidable condition `(σ(n) - n - 1) ∣ (n - 1)`. -/
lemma hyperperfect_iff_dvd {n : ℕ} (hn : n + 1 < sigmaOne n) :
    Hyperperfect n ↔ (sigmaOne n - (n + 1)) ∣ (n - 1) := by
  have hn2 : 2 ≤ n := by
    rcases n with _ | _ | n
    · simp [sigmaOne_zero] at hn
    · simp [sigmaOne_one] at hn
    · omega
  constructor
  · rintro ⟨k, hk, hEq⟩
    refine ⟨k, ?_⟩
    have h1 : ((n : ℤ) - 1) = ((sigmaOne n : ℤ) - ((n : ℤ) + 1)) * (k : ℤ) := by linarith
    have h2 : ((n - 1 : ℕ) : ℤ) = ((sigmaOne n - (n + 1) : ℕ) : ℤ) * (k : ℤ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : n + 1 ≤ sigmaOne n)]
      push_cast
      linarith
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    · have h2 : ((n - 1 : ℕ) : ℤ) = ((sigmaOne n - (n + 1) : ℕ) : ℤ) * (k : ℤ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hk
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : n + 1 ≤ sigmaOne n)] at h2
      push_cast at h2 ⊢
      linarith

/-! ## Concrete hyperperfect numbers (unconditional) -/

lemma hyperperfect_six : Hyperperfect 6 :=
  hyperperfect_mul_of_primes (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)

lemma hyperperfect_twentyone : Hyperperfect 21 :=
  hyperperfect_mul_of_primes (p := 3) (q := 7) (by norm_num) (by norm_num) (by norm_num)

lemma hyperperfect_threehundredone : Hyperperfect 301 :=
  hyperperfect_mul_of_primes (p := 7) (q := 43) (by norm_num) (by norm_num) (by norm_num)

lemma hyperperfect_twentyfortyone : Hyperperfect 2041 :=
  hyperperfect_mul_of_primes (p := 13) (q := 157) (by norm_num) (by norm_num) (by norm_num)

/-- `325 = 5² · 13` is `3`-hyperperfect; it lies outside the family above, and is checked
by the decidable criterion. -/
lemma hyperperfect_threehundredtwentyfive : Hyperperfect 325 := by
  rw [hyperperfect_iff_dvd (by decide)]
  decide

/-! ## Main conditional theorem -/

/-- The set of primes `p` for which `p² - p + 1` is also prime. -/
def GoodPrimes : Set ℕ := {p : ℕ | p.Prime ∧ Nat.Prime (p * p + 1 - p)}

/-- **Hyperperfect Infinitude (conditional reduction).**
If there are infinitely many primes `p` such that `p² - p + 1` is also prime, then there
are infinitely many hyperperfect numbers.  Each such `p` yields the `(p-1)`-hyperperfect
number `p (p² - p + 1)`; e.g. `p = 2, 3, 7, 13` give `6, 21, 301, 2041`. -/
theorem HyperperfectInfinitude (H : GoodPrimes.Infinite) :
    {n : ℕ | Hyperperfect n}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨p, ⟨hp, hq⟩, hpN⟩ := H.exists_gt N
  have hp2 : 2 ≤ p := hp.two_le
  set q := p * p + 1 - p with hqdef
  have hple : p ≤ p * p + 1 := by nlinarith
  have hpq : q + p = p * p + 1 := by omega
  have hmem : p * q ∈ {n : ℕ | Hyperperfect n} := hyperperfect_mul_of_primes hp hq hpq
  have hle : p * q ≤ N := hN hmem
  have hq1 : 1 ≤ q := hq.one_lt.le.trans' (by norm_num)
  have hpp : p ≤ p * q := Nat.le_mul_of_pos_right p hq1
  omega

end Brockian.HyperperfectNumbers

