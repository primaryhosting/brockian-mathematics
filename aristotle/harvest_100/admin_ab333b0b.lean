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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.HyperperfectNumbers

open scoped BigOperators

/-- `n` is `k`-hyperperfect if `n > 1` and `n = 1 + k * (σ(n) - n - 1)`, i.e. `n` is one plus
`k` times the sum of the divisors of `n` other than `1` and `n`. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  1 < n ∧ n = 1 + k * (ArithmeticFunction.sigma 1 n - n - 1)

/-- The sum of divisors of a product of two distinct primes. -/
lemma sigma_one_prime_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ArithmeticFunction.sigma 1 (p * q) = (p + 1) * (q + 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply,
    hp.sum_divisors, hq.sum_divisors]

/-- Characterisation of `k`-hyperperfectness for a product of two distinct primes. -/
lemma isHyperperfect_prime_mul_prime_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) : IsHyperperfect k (p * q) ↔ p * q = 1 + k * (p + q) := by
  have hσ : ArithmeticFunction.sigma 1 (p * q) - p * q - 1 = p + q := by
    rw [sigma_one_prime_mul_prime hp hq hne]; ring_nf; omega
  constructor
  · rintro ⟨-, h⟩; rw [hσ] at h; exact h
  · intro h
    refine ⟨?_, by rw [hσ]; exact h⟩
    have := hp.two_le
    have := hq.two_le
    nlinarith

/-- Sufficient condition: if `d * e = k ^ 2 + 1` and both `k + d` and `k + e` are prime, then
`(k + d) * (k + e)` is `k`-hyperperfect. -/
lemma isHyperperfect_of_factorization {k d e : ℕ} (hk : 1 ≤ k) (hde : d * e = k ^ 2 + 1)
    (hp : Nat.Prime (k + d)) (hq : Nat.Prime (k + e)) :
    IsHyperperfect k ((k + d) * (k + e)) := by
  have hne : k + d ≠ k + e := by
    intro h
    have hd : d = e := by omega
    subst hd
    have h1 : k < d := by nlinarith
    have h2 : d ≤ k := by nlinarith
    omega
  rw [isHyperperfect_prime_mul_prime_iff hp hq hne]
  nlinarith [hde]

/-- The Brockian hypothesis: for every `k ≥ 1` the number `k ^ 2 + 1` admits a factorisation
`d * e` such that both `k + d` and `k + e` are prime. -/
def BrockianFactorizationHypothesis : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ d e : ℕ, d * e = k ^ 2 + 1 ∧ Nat.Prime (k + d) ∧ Nat.Prime (k + e)

/-- **Conditional reduction of the "hyperperfect number for every `k`" conjecture.**
Assuming that for every `k ≥ 1` one can factor `k ^ 2 + 1 = d * e` with `k + d` and `k + e`
prime, every `k ≥ 1` admits a `k`-hyperperfect number. -/
theorem HyperperfectAllK (hBrock : BrockianFactorizationHypothesis) :
    ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, IsHyperperfect k n := by
  intro k hk
  obtain ⟨d, e, hde, hp, hq⟩ := hBrock k hk
  exact ⟨_, isHyperperfect_of_factorization hk hde hp hq⟩

/-- The simplest instance of the criterion: if `k + 1` and `k ^ 2 + k + 1` are both prime, then
`(k + 1) * (k ^ 2 + k + 1)` is `k`-hyperperfect. -/
theorem isHyperperfect_of_prime_prime {k : ℕ} (hk : 1 ≤ k) (hp : Nat.Prime (k + 1))
    (hq : Nat.Prime (k ^ 2 + k + 1)) :
    IsHyperperfect k ((k + 1) * (k ^ 2 + k + 1)) := by
  have h : k + (k ^ 2 + 1) = k ^ 2 + k + 1 := by ring
  have := isHyperperfect_of_factorization (d := 1) (e := k ^ 2 + 1) hk (by ring)
    (by simpa using hp) (by rw [h]; exact hq)
  simpa [h] using this

/-! ### A second family: `p ^ 2 * q` -/

/-- The sum of divisors of `p ^ 2 * q` for distinct primes `p`, `q`. -/
lemma sigma_one_prime_sq_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ArithmeticFunction.sigma 1 (p ^ 2 * q) = (1 + p + p ^ 2) * (q + 1) := by
  have hcop : Nat.Coprime (p ^ 2) q := ((Nat.coprime_primes hp hq).2 hne).pow_left 2
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply,
    hq.sum_divisors, Nat.sum_divisors_prime_pow hp]
  simp [Finset.sum_range_succ]

/-- Characterisation of `k`-hyperperfectness for numbers of the shape `p ^ 2 * q` with `p`, `q`
distinct primes. -/
lemma isHyperperfect_prime_sq_mul_prime_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) :
    IsHyperperfect k (p ^ 2 * q) ↔ p ^ 2 * q = 1 + k * ((p + 1) * (p + q)) := by
  have key : (1 + p + p ^ 2) * (q + 1) = p ^ 2 * q + 1 + (p + 1) * (p + q) := by ring
  have hσ : ArithmeticFunction.sigma 1 (p ^ 2 * q) - p ^ 2 * q - 1 = (p + 1) * (p + q) := by
    rw [sigma_one_prime_sq_mul_prime hp hq hne, key]; omega
  constructor
  · rintro ⟨-, h⟩; rw [hσ] at h; exact h
  · intro h
    refine ⟨?_, by rw [hσ]; exact h⟩
    have := hp.two_le
    have := hq.two_le
    nlinarith

/-! ### Unconditional instances -/

/-- `6` is a (1-)perfect number. -/
theorem isHyperperfect_one_six : IsHyperperfect 1 6 := by
  have := isHyperperfect_of_prime_prime (k := 1) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `21` is 2-hyperperfect. -/
theorem isHyperperfect_two_twentyOne : IsHyperperfect 2 21 := by
  have := isHyperperfect_of_prime_prime (k := 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `301` is 6-hyperperfect. -/
theorem isHyperperfect_six_threeHundredOne : IsHyperperfect 6 301 := by
  have := isHyperperfect_of_prime_prime (k := 6) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `697` is 12-hyperperfect. -/
theorem isHyperperfect_twelve : IsHyperperfect 12 697 := by
  have := (isHyperperfect_prime_mul_prime_iff (k := 12) (p := 17) (q := 41)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

/-- `1333` is 18-hyperperfect. -/
theorem isHyperperfect_eighteen : IsHyperperfect 18 1333 := by
  have := (isHyperperfect_prime_mul_prime_iff (k := 18) (p := 31) (q := 43)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

/-- `3901` is 30-hyperperfect. -/
theorem isHyperperfect_thirty : IsHyperperfect 30 3901 := by
  have := (isHyperperfect_prime_mul_prime_iff (k := 30) (p := 47) (q := 83)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

/-- `26977` is 48-hyperperfect. -/
theorem isHyperperfect_fortyEight : IsHyperperfect 48 26977 := by
  have := (isHyperperfect_prime_mul_prime_iff (k := 48) (p := 53) (q := 509)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

/-- `24601` is 60-hyperperfect. -/
theorem isHyperperfect_sixty : IsHyperperfect 60 24601 := by
  have := (isHyperperfect_prime_mul_prime_iff (k := 60) (p := 73) (q := 337)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

/-- `325 = 5 ^ 2 * 13` is 3-hyperperfect. -/
theorem isHyperperfect_three : IsHyperperfect 3 325 := by
  have := (isHyperperfect_prime_sq_mul_prime_iff (k := 3) (p := 5) (q := 13)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

/-- `10693 = 17 ^ 2 * 37` is 11-hyperperfect. -/
theorem isHyperperfect_eleven : IsHyperperfect 11 10693 := by
  have := (isHyperperfect_prime_sq_mul_prime_iff (k := 11) (p := 17) (q := 37)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

end Brockian.HyperperfectNumbers

