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

-- (The header above is repeated here as a module docstring; a `/-!` block cannot precede
-- `import` in Lean 4.)
/-!
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `n` is **`k`-hyperperfect** when `n = 1 + k * (σ n - n - 1)`, i.e. when
`k * σ n + 1 = (k + 1) * n + k`, where `σ n` is the sum of the divisors of `n`.
(The second, subtraction-free form is the one used here; `hyperperfect_iff_classical`
shows it agrees with the classical definition.) -/
def IsHyperperfect (k n : ℕ) : Prop :=
  1 < n ∧ k * (∑ d ∈ n.divisors, d) + 1 = (k + 1) * n + k

/-- The definition used here agrees with the classical formula
`n = 1 + k * (σ n - n - 1)`, read over the integers. -/
theorem hyperperfect_iff_classical (k n : ℕ) :
    IsHyperperfect k n ↔
      1 < n ∧ (n : ℤ) = 1 + k * (((∑ d ∈ n.divisors, d : ℕ) : ℤ) - n - 1) := by
  unfold IsHyperperfect
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h2' : (k : ℤ) * ((∑ d ∈ n.divisors, d : ℕ) : ℤ) + 1 = ((k : ℤ) + 1) * n + k := by
      exact_mod_cast h2
    linarith [h2']
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have : (k : ℤ) * ((∑ d ∈ n.divisors, d : ℕ) : ℤ) + 1 = ((k : ℤ) + 1) * n + k := by
      linarith [h2]
    exact_mod_cast this

/-- Sum of divisors of a product of two distinct primes. -/
theorem sum_divisors_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∑ d ∈ (p * q).divisors, d = (p + 1) * (q + 1) := by
  rw [Nat.Coprime.sum_divisors_mul ((Nat.coprime_primes hp hq).mpr hpq), hp.sum_divisors,
    hq.sum_divisors]

/-- **Characterisation of hyperperfect semiprimes.** For distinct primes `p, q`, the number
`p * q` is `k`-hyperperfect exactly when `p * q = k * (p + q) + 1`, equivalently
`(p - k) * (q - k) = k ^ 2 + 1`. -/
theorem hyperperfect_semiprime_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsHyperperfect k (p * q) ↔ p * q = k * (p + q) + 1 := by
  have h2p := hp.two_le
  have h2q := hq.two_le
  unfold IsHyperperfect
  rw [sum_divisors_mul_primes hp hq hpq]
  constructor
  · rintro ⟨-, h⟩
    nlinarith [h]
  · intro h
    refine ⟨?_, by nlinarith [h]⟩
    nlinarith

/-- **Main construction.** Every factorisation `d * e = k ^ 2 + 1` with `d + k` and `e + k`
distinct primes yields the `k`-hyperperfect number `(d + k) * (e + k)`. -/
theorem hyperperfect_of_factorization {k d e : ℕ} (hde : d * e = k * k + 1)
    (hp : Nat.Prime (d + k)) (hq : Nat.Prime (e + k)) (hne : d ≠ e) :
    IsHyperperfect k ((d + k) * (e + k)) := by
  have hpq : d + k ≠ e + k := by omega
  rw [hyperperfect_semiprime_iff hp hq hpq]
  zify at hde ⊢
  linear_combination hde

/-- Sum of divisors of `p ^ 2 * q` for distinct primes `p, q`. -/
theorem sum_divisors_sq_mul_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∑ d ∈ (p ^ 2 * q).divisors, d = (1 + p + p ^ 2) * (q + 1) := by
  rw [Nat.Coprime.sum_divisors_mul (Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp hq).mpr hpq)),
    hq.sum_divisors, Nat.sum_divisors_prime_pow hp]
  simp [Finset.sum_range_succ]

/-- **Characterisation of hyperperfect numbers of the shape `p ^ 2 * q`.**  For distinct
primes `p, q`, the number `p ^ 2 * q` is `k`-hyperperfect exactly when
`q * (p ^ 2 - k * p - k) = k * p ^ 2 + k * p + 1` (written subtraction-free). -/
theorem hyperperfect_sq_mul_prime_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsHyperperfect k (p ^ 2 * q) ↔ q * p ^ 2 = q * (k * p + k) + (k * p ^ 2 + k * p + 1) := by
  have h2p := hp.two_le
  have h2q := hq.two_le
  unfold IsHyperperfect
  rw [sum_divisors_sq_mul_prime hp hq hpq]
  constructor
  · rintro ⟨-, h⟩
    nlinarith [h]
  · intro h
    refine ⟨by nlinarith, by nlinarith [h]⟩

/-- **Hyperperfect All K (partial result).**
The Minoli–Bear conjecture asserts that for *every* `k ≥ 1` there is a `k`-hyperperfect
number; this is open.  What is proved here is an unconditional criterion: a `k`-hyperperfect
number exists for every `k ≥ 1` such that either

* `k ^ 2 + 1` factors as `d * e` with `d + k` and `e + k` distinct primes — then
  `(d + k) * (e + k)` is `k`-hyperperfect (this covers `k = 1, 2, 6, …`), or
* there are distinct primes `p, q` with `q * (p ^ 2 - k * p - k) = k * p ^ 2 + k * p + 1` —
  then `p ^ 2 * q` is `k`-hyperperfect (this covers `k = 3` via `325 = 5 ^ 2 * 13`, etc.). -/
theorem HyperperfectAllK :
    ∀ k : ℕ, 0 < k →
      ((∃ d e : ℕ, d * e = k * k + 1 ∧ Nat.Prime (d + k) ∧ Nat.Prime (e + k) ∧ d ≠ e) ∨
        (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
          q * p ^ 2 = q * (k * p + k) + (k * p ^ 2 + k * p + 1))) →
      ∃ n : ℕ, IsHyperperfect k n := by
  rintro k - (⟨d, e, hde, hp, hq, hne⟩ | ⟨p, q, hp, hq, hpq, h⟩)
  · exact ⟨(d + k) * (e + k), hyperperfect_of_factorization hde hp hq hne⟩
  · exact ⟨p ^ 2 * q, (hyperperfect_sq_mul_prime_iff hp hq hpq).mpr h⟩

/-- The classical special case `d = 1`: if `k + 1` and `k ^ 2 + k + 1` are both prime, then
`(k + 1) * (k ^ 2 + k + 1)` is `k`-hyperperfect. -/
theorem hyperperfect_of_prime_pair {k : ℕ} (hk : 0 < k) (hp : Nat.Prime (k + 1))
    (hq : Nat.Prime (k * k + k + 1)) :
    IsHyperperfect k ((k + 1) * (k * k + k + 1)) := by
  have h : (1 : ℕ) + k = k + 1 := by omega
  have h2 : (k * k + 1) + k = k * k + k + 1 := by omega
  have := hyperperfect_of_factorization (k := k) (d := 1) (e := k * k + 1)
    (by ring) (by rw [h]; exact hp) (by rw [h2]; exact hq) (by nlinarith)
  rw [h, h2] at this
  exact this

/-- The criterion of `HyperperfectAllK` is satisfiable, e.g. for `k = 1`: `6` is perfect. -/
theorem isHyperperfect_one_six : IsHyperperfect 1 6 := by
  refine ⟨by norm_num, by decide⟩

/-- `21` is `2`-hyperperfect. -/
theorem isHyperperfect_two_21 : IsHyperperfect 2 21 := by
  refine ⟨by norm_num, by decide⟩

/-- `325` is `3`-hyperperfect (note it is *not* a semiprime, so it lies outside the family
constructed above). -/
theorem isHyperperfect_three_325 : IsHyperperfect 3 325 := by
  refine ⟨by norm_num, by decide⟩

/-- The criterion of `HyperperfectAllK` is applicable at `k = 1` (first branch, giving `6`). -/
theorem exists_hyperperfect_one : ∃ n : ℕ, IsHyperperfect 1 n :=
  HyperperfectAllK 1 one_pos (Or.inl ⟨1, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩)

/-- The criterion of `HyperperfectAllK` is applicable at `k = 3` (second branch, giving `325`). -/
theorem exists_hyperperfect_three : ∃ n : ℕ, IsHyperperfect 3 n :=
  HyperperfectAllK 3 (by norm_num)
    (Or.inr ⟨5, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩)

/-- `301` is `6`-hyperperfect. -/
theorem isHyperperfect_six_301 : IsHyperperfect 6 301 := by
  refine ⟨by norm_num, by decide⟩

end Brockian.HyperperfectNumbers

