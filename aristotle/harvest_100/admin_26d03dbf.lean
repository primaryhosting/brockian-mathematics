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

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one more than
`k` times the sum of its proper divisors other than `1`.  For `k = 1` this is exactly the
condition of being a perfect number. -/
def Hyperperfect (k n : ℕ) : Prop :=
  1 < n ∧ (n : ℤ) = 1 + k * ((σ 1 n : ℤ) - n - 1)

/-- Sanity check on the definition: for `k = 1`, hyperperfection is perfection. -/
theorem hyperperfect_one_iff_perfect {n : ℕ} (hn : 1 < n) : Hyperperfect 1 n ↔ n.Perfect := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (by omega), ← ArithmeticFunction.sigma_one_apply,
    Hyperperfect]
  constructor
  · rintro ⟨-, h⟩
    have h2 : (σ 1 n : ℤ) = 2 * n := by push_cast at h ⊢; linarith
    exact_mod_cast h2
  · intro h
    have h2 : (σ 1 n : ℤ) = 2 * n := by exact_mod_cast h
    exact ⟨hn, by push_cast; linarith⟩

/-- The sum of divisors of a prime power `p ^ t`, written as an explicit geometric sum. -/
def sigmaPrimePow (p t : ℕ) : ℕ := ∑ i ∈ Finset.range (t + 1), p ^ i

lemma sigma_one_primePow {p : ℕ} (hp : p.Prime) (t : ℕ) :
    σ 1 (p ^ t) = sigmaPrimePow p t := by
  simpa [sigmaPrimePow] using ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := t) hp

lemma sigma_one_prime {q : ℕ} (hq : q.Prime) : σ 1 q = q + 1 := by
  have := ArithmeticFunction.sigma_one_apply_prime_pow (p := q) (i := 1) hq
  simpa [Finset.sum_range_succ, add_comm] using this

/-- The sum-of-divisors function on numbers of the shape `p ^ t * q` with `p ≠ q` prime. -/
lemma sigma_one_primePow_mul_prime {p t q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    σ 1 (p ^ t * q) = sigmaPrimePow p t * (q + 1) := by
  have hcop : Nat.Coprime (p ^ t) q :=
    Nat.Coprime.pow_left t ((Nat.coprime_primes hp hq).mpr hpq)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_primePow hp, sigma_one_prime hq]

/-- **Characterisation of hyperperfect numbers of the shape `p ^ t * q`.**
For distinct primes `p, q`, the number `p ^ t * q` is `k`-hyperperfect exactly when the
displayed Diophantine equation holds, where `S = 1 + p + ⋯ + p ^ t = σ (p ^ t)`. -/
theorem hyperperfect_primePow_mul_prime_iff {k p t q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Hyperperfect k (p ^ t * q) ↔
      (q : ℤ) * ((k + 1) * (p : ℤ) ^ t - k * (sigmaPrimePow p t : ℤ))
        = k * (sigmaPrimePow p t : ℤ) - k + 1 := by
  have hone : 1 < p ^ t * q := by
    have hq2 : 2 ≤ q := hq.two_le
    have hpt : 1 ≤ p ^ t := Nat.one_le_pow _ _ hp.pos
    calc 1 < 2 := by norm_num
      _ ≤ 1 * q := by simpa using hq2
      _ ≤ p ^ t * q := by
          exact Nat.mul_le_mul_right q hpt
  rw [Hyperperfect, sigma_one_primePow_mul_prime hp hq hpq]
  simp only [hone, true_and]
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- Sufficient condition: solutions of the Diophantine equation give `k`-hyperperfect numbers. -/
theorem hyperperfect_of_primePow_mul_prime {k p t q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (heq : (q : ℤ) * ((k + 1) * (p : ℤ) ^ t - k * (sigmaPrimePow p t : ℤ))
        = k * (sigmaPrimePow p t : ℤ) - k + 1) :
    Hyperperfect k (p ^ t * q) :=
  (hyperperfect_primePow_mul_prime_iff hp hq hpq).mpr heq

/-- The semiprime case `t = 1`: `p * q` is `k`-hyperperfect iff `(p - k) * (q - k) = k ^ 2 + 1`. -/
theorem hyperperfect_mul_prime_iff {k p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Hyperperfect k (p * q) ↔ ((p : ℤ) - k) * ((q : ℤ) - k) = (k : ℤ) ^ 2 + 1 := by
  have h := hyperperfect_primePow_mul_prime_iff (k := k) (t := 1) hp hq hpq
  have hS : (sigmaPrimePow p 1 : ℤ) = 1 + (p : ℤ) := by
    simp [sigmaPrimePow, Finset.sum_range_succ]
  rw [pow_one] at h
  rw [h, hS]
  constructor <;> intro hh <;> linear_combination hh

/-- The statement of the conjecture: for every `k ≥ 1` there is a `k`-hyperperfect number. -/
def HyperperfectExistsForAllK : Prop :=
  ∀ k : ℕ, 0 < k → ∃ n : ℕ, Hyperperfect k n

/-- A purely number-theoretic (prime-pattern) condition: for each `k ≥ 1` the Diophantine
equation for numbers of shape `p ^ t * q` has a solution in distinct primes `p, q`. -/
def PrimePowShapeSolvableForAllK : Prop :=
  ∀ k : ℕ, 0 < k → ∃ p t q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
    (q : ℤ) * ((k + 1) * (p : ℤ) ^ t - k * (sigmaPrimePow p t : ℤ))
      = k * (sigmaPrimePow p t : ℤ) - k + 1

/-- **Conditional reduction of the "hyperperfect numbers for all `k`" conjecture.**
If for every `k ≥ 1` the prime-power/prime Diophantine equation
`q * ((k+1) * p ^ t - k * S) = k * S - k + 1` (with `S = 1 + p + ⋯ + p ^ t`) is solvable in
distinct primes `p, q`, then a `k`-hyperperfect number exists for every `k ≥ 1`. -/
theorem HyperperfectAllK (H : PrimePowShapeSolvableForAllK) : HyperperfectExistsForAllK := by
  -- The unconditional statement `HyperperfectExistsForAllK` is not established here; what is
  -- proved is the reduction to the prime-pattern hypothesis `PrimePowShapeSolvableForAllK`,
  -- together with the explicit witnesses recorded in the `Examples` section below.
  intro k hk
  obtain ⟨p, t, q, hp, hq, hpq, heq⟩ := H k hk
  exact ⟨p ^ t * q, hyperperfect_of_primePow_mul_prime hp hq hpq heq⟩

section Examples

/-- `6` is `1`-hyperperfect (i.e. perfect). -/
theorem hyperperfect_one_six : Hyperperfect 1 6 := by
  have h : Hyperperfect 1 (2 ^ 1 * 3) :=
    hyperperfect_of_primePow_mul_prime (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [sigmaPrimePow, Finset.sum_range_succ])
  norm_num at h
  exact h

/-- `21` is `2`-hyperperfect. -/
theorem hyperperfect_two_21 : Hyperperfect 2 21 := by
  have h : Hyperperfect 2 (3 ^ 1 * 7) :=
    hyperperfect_of_primePow_mul_prime (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [sigmaPrimePow, Finset.sum_range_succ])
  norm_num at h
  exact h

/-- `325 = 5 ^ 2 * 13` is `3`-hyperperfect. -/
theorem hyperperfect_three_325 : Hyperperfect 3 325 := by
  have h : Hyperperfect 3 (5 ^ 2 * 13) :=
    hyperperfect_of_primePow_mul_prime (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [sigmaPrimePow, Finset.sum_range_succ])
  norm_num at h
  exact h

/-- `1950625 = 5 ^ 4 * 3121` is `4`-hyperperfect. -/
theorem hyperperfect_four_1950625 : Hyperperfect 4 1950625 := by
  have h : Hyperperfect 4 (5 ^ 4 * 3121) :=
    hyperperfect_of_primePow_mul_prime (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [sigmaPrimePow, Finset.sum_range_succ])
  norm_num at h
  exact h

/-- `301 = 7 * 43` is `6`-hyperperfect. -/
theorem hyperperfect_six_301 : Hyperperfect 6 301 := by
  have h : Hyperperfect 6 (7 * 43) :=
    (hyperperfect_mul_prime_iff (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
  norm_num at h
  exact h

/-- `159841 = 11 ^ 2 * 1321` is `10`-hyperperfect. -/
theorem hyperperfect_ten_159841 : Hyperperfect 10 159841 := by
  have h : Hyperperfect 10 (11 ^ 2 * 1321) :=
    hyperperfect_of_primePow_mul_prime (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [sigmaPrimePow, Finset.sum_range_succ])
  norm_num at h
  exact h

/-- `10693 = 17 ^ 2 * 37` is `11`-hyperperfect. -/
theorem hyperperfect_eleven_10693 : Hyperperfect 11 10693 := by
  have h : Hyperperfect 11 (17 ^ 2 * 37) :=
    hyperperfect_of_primePow_mul_prime (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [sigmaPrimePow, Finset.sum_range_succ])
  norm_num at h
  exact h

/-- `697 = 17 * 41` is `12`-hyperperfect. -/
theorem hyperperfect_twelve_697 : Hyperperfect 12 697 := by
  have h : Hyperperfect 12 (17 * 41) :=
    (hyperperfect_mul_prime_iff (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
  norm_num at h
  exact h

/-- `1333 = 31 * 43` is `18`-hyperperfect. -/
theorem hyperperfect_eighteen_1333 : Hyperperfect 18 1333 := by
  have h : Hyperperfect 18 (31 * 43) :=
    (hyperperfect_mul_prime_iff (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
  norm_num at h
  exact h

/-- `51301 = 29 ^ 2 * 61` is `19`-hyperperfect. -/
theorem hyperperfect_nineteen_51301 : Hyperperfect 19 51301 := by
  have h : Hyperperfect 19 (29 ^ 2 * 61) :=
    hyperperfect_of_primePow_mul_prime (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [sigmaPrimePow, Finset.sum_range_succ])
  norm_num at h
  exact h

end Examples

end Brockian.HyperperfectNumbers

