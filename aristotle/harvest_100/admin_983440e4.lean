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

open scoped BigOperators
open scoped Nat
open ArithmeticFunction

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`.  Written without truncated
subtraction this reads `k * σ n + 1 = (k + 1) * n + k`.  For `k = 1` this is exactly
the condition that `n` is a perfect number. -/
def Hyperperfect (k n : ℕ) : Prop :=
  1 < n ∧ k * (sigma 1 n) + 1 = (k + 1) * n + k

/-- The defining equation of `Hyperperfect` is equivalent to the usual formulation
`n = 1 + k * (σ n - n - 1)` (using truncated subtraction on `ℕ`), whenever `n` divides
itself into `σ n`, i.e. whenever `n + 1 ≤ σ n`. -/
theorem hyperperfect_iff {k n : ℕ} (hn : n + 1 ≤ sigma 1 n) :
    Hyperperfect k n ↔ 1 < n ∧ n = 1 + k * (sigma 1 n - n - 1) := by
  unfold Hyperperfect
  have hexp : (k + 1) * n = k * n + n := by ring
  have key : k * (sigma 1 n - n - 1) = k * sigma 1 n - k * n - k := by
    rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one]
  have hle : k * n + k ≤ k * sigma 1 n := by
    have h := Nat.mul_le_mul_left k hn
    rw [Nat.mul_add, Nat.mul_one] at h
    exact h
  rw [hexp, key]
  omega

/-! ### Sum-of-divisors computations -/

/-- The sum of divisors of a prime `p` is `p + 1`. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega

/-- The sum of divisors of a prime power. -/
lemma sigma_one_prime_pow {p a : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]

/-- The sum of divisors of `p ^ a * q` for distinct primes `p`, `q`. -/
lemma sigma_one_prime_pow_mul_prime {p q a : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    sigma 1 (p ^ a * q) = (∑ i ∈ Finset.range (a + 1), p ^ i) * (q + 1) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime
      (Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hq).2 hne)),
    sigma_one_prime_pow hp, sigma_one_prime hq]

/-! ### A construction of hyperperfect numbers -/

/-- A *witness* for `k`: a prime power times a prime, `n = p ^ a * q`, satisfying the
hyperperfection equation `k * σ n + 1 = (k + 1) * n + k`. -/
def Witness (k p a q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p ≠ q ∧ 1 ≤ a ∧
    k * ((∑ i ∈ Finset.range (a + 1), p ^ i) * (q + 1)) + 1 = (k + 1) * (p ^ a * q) + k

/-- **Construction.**  A witness for `k` yields a `k`-hyperperfect number. -/
theorem hyperperfect_of_witness {k p a q : ℕ} (h : Witness k p a q) :
    Hyperperfect k (p ^ a * q) := by
  obtain ⟨hp, hq, hne, ha, heq⟩ := h
  refine ⟨?_, ?_⟩
  · have h2 : 2 ≤ p ^ a := by
      calc 2 = 2 ^ 1 := rfl
      _ ≤ p ^ 1 := Nat.pow_le_pow_left hp.two_le 1
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
    have := hq.two_le
    nlinarith
  · rw [sigma_one_prime_pow_mul_prime hp hq hne]
    exact heq

/-- **The semiprime case.**  If `a * b = k ^ 2 + 1` and `k + a`, `k + b` are distinct primes,
then `(k + a) * (k + b)` is `k`-hyperperfect.  (Equivalently: for distinct primes `p, q`,
the number `p * q` is `k`-hyperperfect iff `(p - k) * (q - k) = k ^ 2 + 1`.) -/
theorem hyperperfect_mul_of_primes {k a b : ℕ} (hab : a * b = k ^ 2 + 1)
    (hp : (k + a).Prime) (hq : (k + b).Prime) (hne : a ≠ b) :
    Hyperperfect k ((k + a) * (k + b)) := by
  have hpq : k + a ≠ k + b := by omega
  have hwit : Witness k (k + a) 1 (k + b) := by
    refine ⟨hp, hq, hpq, le_refl 1, ?_⟩
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
    nlinarith [hab]
  have := hyperperfect_of_witness hwit
  simpa using this

/-- **Characterisation in the semiprime case.**  For distinct primes `p` and `q`, the number
`p * q` is `k`-hyperperfect exactly when `k * p + k * q + 1 = p * q`, i.e. (over `ℤ`)
when `(p - k) * (q - k) = k ^ 2 + 1`. -/
theorem hyperperfect_mul_primes_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Hyperperfect k (p * q) ↔ k * p + k * q + 1 = p * q := by
  have hs : sigma 1 (p * q) = (p + 1) * (q + 1) := by
    have := sigma_one_prime_pow_mul_prime (p := p) (q := q) (a := 1) hp hq hne
    simpa [Finset.sum_range_succ, Nat.add_comm] using this
  have h2 := hp.two_le
  have h3 := hq.two_le
  constructor
  · rintro ⟨-, h⟩
    rw [hs] at h
    nlinarith [h]
  · intro h
    refine ⟨by nlinarith, ?_⟩
    rw [hs]
    nlinarith [h]

/-- The Minoli-type family: if `k + 1` and `k ^ 2 + k + 1` are both prime, then
`(k + 1) * (k ^ 2 + k + 1)` is `k`-hyperperfect. -/
theorem hyperperfect_of_prime_pair {k : ℕ} (hk : 0 < k) (h1 : (k + 1).Prime)
    (h2 : (k ^ 2 + k + 1).Prime) :
    Hyperperfect k ((k + 1) * (k ^ 2 + k + 1)) := by
  have h : (k + (k ^ 2 + 1)) = k ^ 2 + k + 1 := by ring
  have := hyperperfect_mul_of_primes (k := k) (a := 1) (b := k ^ 2 + 1) (by ring)
    (by simpa using h1) (by rw [h]; exact h2) (by nlinarith)
  simpa [h] using this

/-! ### Explicit hyperperfect numbers -/

private lemma wit {k p a q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (ha : 1 ≤ a)
    (heq : k * ((∑ i ∈ Finset.range (a + 1), p ^ i) * (q + 1)) + 1 = (k + 1) * (p ^ a * q) + k) :
    ∃ n, Hyperperfect k n :=
  ⟨_, hyperperfect_of_witness ⟨hp, hq, hne, ha, heq⟩⟩

/-- `6` is `1`-hyperperfect, i.e. perfect. -/
theorem hyperperfect_one_six : Hyperperfect 1 6 := by
  have := hyperperfect_of_witness (k := 1) (p := 2) (a := 1) (q := 3)
    ⟨by norm_num, by norm_num, by norm_num, le_refl 1, by decide⟩
  norm_num at this
  exact this

/-- `21` is `2`-hyperperfect. -/
theorem hyperperfect_two_21 : Hyperperfect 2 21 := by
  have := hyperperfect_of_witness (k := 2) (p := 3) (a := 1) (q := 7)
    ⟨by norm_num, by norm_num, by norm_num, le_refl 1, by decide⟩
  norm_num at this
  exact this

/-- `325 = 5 ^ 2 * 13` is `3`-hyperperfect. -/
theorem hyperperfect_three_325 : Hyperperfect 3 325 := by
  have := hyperperfect_of_witness (k := 3) (p := 5) (a := 2) (q := 13)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide⟩
  norm_num at this
  exact this

/-- `301 = 7 * 43` is `6`-hyperperfect. -/
theorem hyperperfect_six_301 : Hyperperfect 6 301 := by
  have := hyperperfect_of_witness (k := 6) (p := 7) (a := 1) (q := 43)
    ⟨by norm_num, by norm_num, by norm_num, le_refl 1, by decide⟩
  norm_num at this
  exact this

/-- For each `k` in an explicit finite list, a `k`-hyperperfect number exists.
This gives unconditional instances of the conjecture below. -/
theorem exists_hyperperfect_of_mem_list :
    ∀ k ∈ ({1, 2, 3, 4, 6, 10, 11, 12, 18, 19, 30, 31, 35, 48, 59, 60} : Finset ℕ),
      ∃ n, Hyperperfect k n := by
  intro k hk
  fin_cases hk
  · exact wit (p := 2) (a := 1) (q := 3) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 3) (a := 1) (q := 7) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 5) (a := 2) (q := 13) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide)
  · exact wit (p := 5) (a := 4) (q := 3121) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 7) (a := 1) (q := 43) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 11) (a := 2) (q := 1321) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 17) (a := 2) (q := 37) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 17) (a := 1) (q := 41) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 31) (a := 1) (q := 43) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 29) (a := 2) (q := 61) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 47) (a := 1) (q := 83) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 47) (a := 2) (q := 97) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 53) (a := 2) (q := 109) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 53) (a := 1) (q := 509) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)
  · exact wit (p := 89) (a := 2) (q := 181) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Finset.sum_range_succ])
  · exact wit (p := 73) (a := 1) (q := 337) (by norm_num) (by norm_num) (by norm_num)
      (le_refl 1) (by decide)

/-! ### The conjecture -/

/-- The statement "for every `k ≥ 1` there is a `k`-hyperperfect number". -/
def HyperperfectAllKStatement : Prop := ∀ k : ℕ, 0 < k → ∃ n : ℕ, Hyperperfect k n

/-- **Conditional reduction of the "hyperperfect numbers exist for every `k`" conjecture.**

No unconditional proof that every `k ≥ 1` admits a `k`-hyperperfect number is given here.
What is proved is a reduction: it suffices to produce, for each `k ≥ 1`, a witness of the shape
`p ^ a * q` (a prime power times a distinct prime) satisfying the hyperperfection equation.
All the explicit examples above are of this shape, and `exists_hyperperfect_of_mem_list`
verifies the hypothesis unconditionally for the listed values of `k`. -/
theorem HyperperfectAllK
    (H : ∀ k : ℕ, 0 < k → ∃ p a q : ℕ, Witness k p a q) :
    HyperperfectAllKStatement := by
  intro k hk
  obtain ⟨p, a, q, hw⟩ := H k hk
  exact ⟨p ^ a * q, hyperperfect_of_witness hw⟩

end Brockian.HyperperfectNumbers

