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

open Finset

/-- `Hyperperfect k n` says that `n` is a *`k`-hyperperfect number*, i.e. `n > 1` and
`n = 1 + k * (σ(n) - n - 1)`, where `σ(n) = ∑ d ∣ n, d`.

The defining equation is written in the subtraction-free form
`(k + 1) * n + k = k * σ(n) + 1`, which over the integers is equivalent to
`n = 1 + k * (σ n - n - 1)`. -/
def Hyperperfect (k n : ℕ) : Prop :=
  1 < n ∧ (k + 1) * n + k = k * (∑ d ∈ n.divisors, d) + 1

/-- The subtraction-free defining equation of `Hyperperfect` is equivalent to the usual
form `n = 1 + k * (σ n - n - 1)` stated over `ℤ`. -/
theorem hyperperfect_iff_int (k n : ℕ) :
    Hyperperfect k n ↔
      1 < n ∧ (n : ℤ) = 1 + k * ((∑ d ∈ n.divisors, (d : ℤ)) - n - 1) := by
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    have h' : (((k + 1) * n + k : ℕ) : ℤ)
        = ((k * (∑ d ∈ n.divisors, d) + 1 : ℕ) : ℤ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h
    push_cast at h'
    linarith
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    have : (((k + 1) * n + k : ℕ) : ℤ) = ((k * (∑ d ∈ n.divisors, d) + 1 : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this

/-- The sum of divisors of a product of two distinct primes. -/
theorem sum_divisors_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∑ d ∈ (p * q).divisors, d = (1 + p) * (1 + q) := by
  rw [Nat.Coprime.sum_divisors_mul ((Nat.coprime_primes hp hq).2 hpq),
    hp.divisors, hq.divisors, Finset.sum_pair hp.one_lt.ne, Finset.sum_pair hq.one_lt.ne]

/-- **Characterisation of hyperperfect semiprimes.** For distinct primes `p`, `q`, the number
`p * q` is `k`-hyperperfect exactly when `p * q = k * p + k * q + 1`, i.e. (over `ℤ`)
`(p - k) * (q - k) = k ^ 2 + 1`. -/
theorem hyperperfect_mul_primes_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Hyperperfect k (p * q) ↔ p * q = k * p + k * q + 1 := by
  have hone : 1 < p * q := by
    calc 1 < p := hp.one_lt
    _ ≤ p * q := Nat.le_mul_of_pos_right _ (by have := hq.one_lt; omega)
  rw [Hyperperfect, sum_divisors_mul_primes hp hq hpq]
  constructor
  · rintro ⟨-, h⟩
    nlinarith [h]
  · intro h
    exact ⟨hone, by nlinarith [h]⟩

/-- **Construction of hyperperfect numbers from factorisations of `k ^ 2 + 1`.**
If `d * e = k ^ 2 + 1` with `k ≥ 1` and both `k + d` and `k + e` prime, then
`(k + d) * (k + e)` is a `k`-hyperperfect number. -/
theorem hyperperfect_of_factorization {k d e : ℕ} (hk : 1 ≤ k) (hde : d * e = k ^ 2 + 1)
    (hp : (k + d).Prime) (hq : (k + e).Prime) : Hyperperfect k ((k + d) * (k + e)) := by
  have hne : d ≠ e := by
    rintro rfl
    rcases Nat.lt_or_ge d (k + 1) with h | h
    · nlinarith
    · nlinarith
  rw [hyperperfect_mul_primes_iff hp hq (by omega)]
  nlinarith [hde]

/-- **Sharpness of the construction.** For `k ≥ 1`, a `k`-hyperperfect number that is a product
of two distinct primes exists *exactly* when `k ^ 2 + 1` factors as `d * e` with `k + d` and
`k + e` both prime. -/
theorem exists_semiprime_hyperperfect_iff {k : ℕ} :
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ Hyperperfect k (p * q)) ↔
      ∃ d e : ℕ, d * e = k ^ 2 + 1 ∧ (k + d).Prime ∧ (k + e).Prime := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, hyp⟩
    rw [hyperperfect_mul_primes_iff hp hq hpq] at hyp
    have hkp : k < p := by
      by_contra hc
      have : p * q ≤ k * q := Nat.mul_le_mul_right q (by omega)
      omega
    have hkq : k < q := by
      by_contra hc
      have : p * q ≤ p * k := Nat.mul_le_mul_left p (by omega)
      nlinarith
    obtain ⟨d, rfl⟩ : ∃ d, p = k + d := ⟨p - k, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e, q = k + e := ⟨q - k, by omega⟩
    exact ⟨d, e, by nlinarith [hyp], hp, hq⟩
  · rintro ⟨d, e, hde, hp, hq⟩
    have hne : d ≠ e := by
      rintro rfl
      rcases Nat.lt_or_ge d (k + 1) with h | h
      · nlinarith [hp.two_le, hq.two_le]
      · nlinarith [hp.two_le, hq.two_le]
    refine ⟨k + d, k + e, hp, hq, by omega, ?_⟩
    rw [hyperperfect_mul_primes_iff hp hq (by omega)]
    nlinarith [hde]

/-- The condition, for each `k ≥ 1`, that `k ^ 2 + 1` admits a factorisation `d * e`
with both `k + d` and `k + e` prime. -/
def PrimeFactorizationCondition : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ d e : ℕ, d * e = k ^ 2 + 1 ∧ (k + d).Prime ∧ (k + e).Prime

/-- The Brockian (Minoli–Bear style) conjecture: for every `k ≥ 1` there is a
`k`-hyperperfect number. -/
def HyperperfectConjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, Hyperperfect k n

/-- **Main result (conditional reduction).** The conjecture that a `k`-hyperperfect number
exists for *every* `k ≥ 1` follows from the purely multiplicative/primality condition
`PrimeFactorizationCondition`: for each `k ≥ 1` one can factor `k ^ 2 + 1 = d * e` so that
`k + d` and `k + e` are both prime. In that case `(k + d) * (k + e)` is `k`-hyperperfect. -/
theorem HyperperfectAllK (h : PrimeFactorizationCondition) : HyperperfectConjecture := by
  intro k hk
  obtain ⟨d, e, hde, hp, hq⟩ := h k hk
  exact ⟨_, hyperperfect_of_factorization hk hde hp hq⟩

/-! ### Unconditional instances -/

theorem hyperperfect_one_six : Hyperperfect 1 6 := by
  have := hyperperfect_of_factorization (k := 1) (d := 1) (e := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at this
  exact this

theorem hyperperfect_two_21 : Hyperperfect 2 21 := by
  have := hyperperfect_of_factorization (k := 2) (d := 1) (e := 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at this
  exact this

theorem hyperperfect_six_301 : Hyperperfect 6 301 := by
  have := hyperperfect_of_factorization (k := 6) (d := 1) (e := 37) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at this
  exact this

theorem hyperperfect_twelve_2041 : Hyperperfect 12 2041 := by
  have := hyperperfect_of_factorization (k := 12) (d := 1) (e := 145) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at this
  exact this

theorem hyperperfect_eighteen_1909 : Hyperperfect 18 1909 := by
  have := hyperperfect_of_factorization (k := 18) (d := 5) (e := 65) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at this
  exact this

theorem hyperperfect_thirty_3901 : Hyperperfect 30 3901 := by
  have := hyperperfect_of_factorization (k := 30) (d := 17) (e := 53) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- The sum of divisors of `p ^ 2 * q` for distinct primes `p`, `q`. -/
theorem sum_divisors_sq_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∑ d ∈ (p ^ 2 * q).divisors, d = (1 + p + p ^ 2) * (1 + q) := by
  rw [Nat.Coprime.sum_divisors_mul
      (Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp hq).2 hpq)),
    hq.divisors, Finset.sum_pair hq.one_lt.ne, Nat.sum_divisors_prime_pow hp]
  simp [Finset.sum_range_succ]

/-- `325 = 5 ^ 2 * 13` is `3`-hyperperfect; note that it is *not* a product of two distinct
primes, so it lies outside the family constructed in `hyperperfect_of_factorization`. -/
theorem hyperperfect_three_325 : Hyperperfect 3 325 := by
  have h : (325 : ℕ) = 5 ^ 2 * 13 := by norm_num
  refine ⟨by norm_num, ?_⟩
  rw [h, sum_divisors_sq_mul_prime (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- `10693 = 17 ^ 2 * 37` is `11`-hyperperfect. -/
theorem hyperperfect_eleven_10693 : Hyperperfect 11 10693 := by
  have h : (10693 : ℕ) = 17 ^ 2 * 37 := by norm_num
  refine ⟨by norm_num, ?_⟩
  rw [h, sum_divisors_sq_mul_prime (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **Unconditional partial result.** For each `k` in `{1, 2, 3, 6, 11, 12, 18, 30}` there is a
`k`-hyperperfect number. -/
theorem exists_hyperperfect_of_mem_known (k : ℕ)
    (hk : k ∈ ({1, 2, 3, 6, 11, 12, 18, 30} : Finset ℕ)) :
    ∃ n : ℕ, Hyperperfect k n := by
  fin_cases hk
  · exact ⟨6, hyperperfect_one_six⟩
  · exact ⟨21, hyperperfect_two_21⟩
  · exact ⟨325, hyperperfect_three_325⟩
  · exact ⟨301, hyperperfect_six_301⟩
  · exact ⟨10693, hyperperfect_eleven_10693⟩
  · exact ⟨2041, hyperperfect_twelve_2041⟩
  · exact ⟨1909, hyperperfect_eighteen_1909⟩
  · exact ⟨3901, hyperperfect_thirty_3901⟩

end Brockian.HyperperfectNumbers

