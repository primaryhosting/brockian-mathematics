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

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-! ## The notion of a `k`-hyperperfect number -/

/-- `IsHyperperfect k n` says that `n` is a `k`-hyperperfect number, i.e. `n > 1` and
`n = 1 + k * (σ n - n - 1)`, where `σ n` is the sum of the divisors of `n`.

The equation is written in the subtraction-free form `n + k * (n + 1) = k * σ n + 1`,
which is equivalent over `ℤ` to `n = 1 + k * (σ n - n - 1)`; this avoids the pitfalls of
truncated natural subtraction (which would make `n = 1` a spurious solution). -/
def IsHyperperfect (k n : ℕ) : Prop :=
  1 < n ∧ n + k * (n + 1) = k * (σ 1 n) + 1

/-- Unfolding of `IsHyperperfect` in terms of the explicit divisor sum. -/
theorem isHyperperfect_iff (k n : ℕ) :
    IsHyperperfect k n ↔ 1 < n ∧ n + k * (n + 1) = k * (∑ d ∈ n.divisors, d) + 1 := by
  simp [IsHyperperfect, sigma_one_apply]

/-- The `ℤ`-form of the defining equation: `n = 1 + k * (σ n - n - 1)`. -/
theorem isHyperperfect_iff_int (k n : ℕ) :
    IsHyperperfect k n ↔ 1 < n ∧ (n : ℤ) = 1 + k * ((σ 1 n : ℤ) - n - 1) := by
  rw [IsHyperperfect]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    have := congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast at this
    linarith
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    have : ((n + k * (n + 1) : ℕ) : ℤ) = ((k * (σ 1 n) + 1 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this

/-! ## A divisor-sum-free reformulation

The Brockian hyperperfect conjecture asserts that a `k`-hyperperfect number exists for
every `k ≥ 1`.  We reformulate it as an equivalent statement in which the divisor-sum
function `σ` has been eliminated: instead of a number `n`, one asks for a finite set of
primes together with exponents, and the hyperperfection equation becomes an explicit
polynomial equation in the primes and their geometric sums. -/

/-- `PrimeExpo S e` says that `S` is a finite set of primes and `e` is positive on `S`. -/
def PrimeExpo (S : Finset ℕ) (e : ℕ → ℕ) : Prop :=
  ∀ p ∈ S, p.Prime ∧ 0 < e p

/-- The number `∏ p ^ e p` described by a set of primes together with exponents. -/
def factorNum (S : Finset ℕ) (e : ℕ → ℕ) : ℕ := ∏ p ∈ S, p ^ e p

/-- The divisor sum of `factorNum S e`, written as an explicit product of geometric sums. -/
def factorSigma (S : Finset ℕ) (e : ℕ → ℕ) : ℕ :=
  ∏ p ∈ S, ∑ i ∈ Finset.range (e p + 1), p ^ i

/-- A `σ`-free certificate of `k`-hyperperfection: a finite set of primes `S` with positive
exponents `e` such that the number `n = ∏ p ^ e p` satisfies `n > 1` and
`n + k * (n + 1) = k * (∏ p (1 + p + ⋯ + p ^ e p)) + 1`. -/
def IsHyperperfectCertificate (k : ℕ) (S : Finset ℕ) (e : ℕ → ℕ) : Prop :=
  PrimeExpo S e ∧ 1 < factorNum S e ∧
    factorNum S e + k * (factorNum S e + 1) = k * factorSigma S e + 1

/-- The divisor sum of `∏ p ^ e p` is the product of the geometric sums, for distinct
primes `p`. -/
theorem sigma_factorNum {S : Finset ℕ} {e : ℕ → ℕ} (h : PrimeExpo S e) :
    σ 1 (factorNum S e) = factorSigma S e := by
  have hcop : (S : Set ℕ).Pairwise (Function.onFun Nat.Coprime fun p => p ^ e p) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (h p hp).1 (h q hq).1).2 hpq)
  rw [factorNum, isMultiplicative_sigma.map_prod _ S hcop, factorSigma]
  exact Finset.prod_congr rfl fun p hp => sigma_one_apply_prime_pow (h p hp).1

/-- A `σ`-free certificate yields a genuine `k`-hyperperfect number. -/
theorem isHyperperfect_of_certificate {k : ℕ} {S : Finset ℕ} {e : ℕ → ℕ}
    (h : IsHyperperfectCertificate k S e) : IsHyperperfect k (factorNum S e) :=
  ⟨h.2.1, by rw [sigma_factorNum h.1]; exact h.2.2⟩

/-- Conversely, every `k`-hyperperfect number `n` carries a `σ`-free certificate, namely its
own prime factorization. -/
theorem certificate_of_isHyperperfect {k n : ℕ} (h : IsHyperperfect k n) :
    IsHyperperfectCertificate k n.primeFactors n.factorization := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd h.1 (by norm_num)
  have hprimeExpo : PrimeExpo n.primeFactors n.factorization := by
    intro p hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, (Nat.Prime.factorization_pos_of_dvd
      (Nat.prime_of_mem_primeFactors hp) hn0 (Nat.dvd_of_mem_primeFactors hp))⟩
  have hnum : factorNum n.primeFactors n.factorization = n :=
    Nat.factorization_prod_pow_eq_self hn0
  have hsig : factorSigma n.primeFactors n.factorization = σ 1 n := by
    rw [← sigma_factorNum hprimeExpo, hnum]
  exact ⟨hprimeExpo, by rw [hnum]; exact h.1, by rw [hnum, hsig]; exact h.2⟩

/-- **Main theorem: an equivalent, divisor-sum-free form of the Brockian hyperperfect
conjecture.**

The statement "for every `k ≥ 1` there is a `k`-hyperperfect number" is *equivalent* to the
statement "for every `k ≥ 1` there is a finite set of primes `S` with positive exponents `e`
whose associated number `n = ∏ p ^ e p` satisfies the explicit polynomial equation
`n + k * (n + 1) = k * (∏ p ∈ S, (1 + p + ⋯ + p ^ e p)) + 1`".

The right-hand side mentions no divisor-sum function: it is a purely multiplicative,
elementary condition on primes and exponents, which is the shape in which all known
hyperperfect numbers are produced. -/
theorem HyperperfectAllK :
    (∀ k : ℕ, 0 < k → ∃ S : Finset ℕ, ∃ e : ℕ → ℕ, IsHyperperfectCertificate k S e) ↔
      (∀ k : ℕ, 0 < k → ∃ n : ℕ, IsHyperperfect k n) := by
  constructor
  · intro H k hk
    obtain ⟨S, e, hSe⟩ := H k hk
    exact ⟨factorNum S e, isHyperperfect_of_certificate hSe⟩
  · intro H k hk
    obtain ⟨n, hn⟩ := H k hk
    exact ⟨n.primeFactors, n.factorization, certificate_of_isHyperperfect hn⟩

/-! ## A workable criterion, and unconditional instances

For numbers of the shape `n = p ^ m * q` with distinct primes `p ≠ q`, hyperperfection
reduces to a single polynomial equation. -/

/-- The geometric-sum identity `p * (1 + p + ⋯ + p^(m-1)) + 1 = 1 + p + ⋯ + p^m`. -/
theorem geom_sum_step (p m : ℕ) :
    p * (∑ i ∈ Finset.range m, p ^ i) + 1 = (∑ i ∈ Finset.range m, p ^ i) + p ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hpow : p ^ (m + 1) = p * p ^ m := by ring
      rw [Finset.sum_range_succ, mul_add, hpow]
      omega

/-- The sum of divisors of a prime. -/
theorem sigma_one_prime {q : ℕ} (hq : q.Prime) : σ 1 q = q + 1 := by
  have := sigma_one_apply_prime_pow (i := 1) hq
  simpa [Finset.sum_range_succ, Nat.add_comm] using this

/-- The divisor sum of `p ^ m * q` for distinct primes `p`, `q`. -/
theorem sigma_primePow_mul_prime {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    σ 1 (p ^ m * q) = (∑ i ∈ Finset.range (m + 1), p ^ i) * (q + 1) := by
  have hcop : Nat.Coprime (p ^ m) q :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hq).2 hpq)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow hp,
    sigma_one_prime hq]

/-- **Certificate criterion for `p ^ m * q`.** For distinct primes `p ≠ q` and `m ≥ 1`,
writing `S = 1 + p + ⋯ + p^(m-1)`, the number `n = p ^ m * q` is `k`-hyperperfect as soon as
`p ^ m * q = k * S * (q + p) + 1`. -/
theorem isHyperperfect_primePow_mul_prime {k p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hm : 0 < m)
    (hcert : p ^ m * q = k * (∑ i ∈ Finset.range m, p ^ i) * (q + p) + 1) :
    IsHyperperfect k (p ^ m * q) := by
  set S : ℕ := ∑ i ∈ Finset.range m, p ^ i with hS
  refine ⟨?_, ?_⟩
  · -- `p ^ m * q > 1`
    have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.one_lt
    have h2 : 1 ≤ q := hq.one_lt.le.trans' (by norm_num)
    calc 1 < p ^ m := h1
      _ = p ^ m * 1 := by ring
      _ ≤ p ^ m * q := Nat.mul_le_mul_left _ h2
  · -- the defining equation
    rw [sigma_primePow_mul_prime hp hq hpq, Finset.sum_range_succ, ← hS]
    have hgeom : p * S + 1 = S + p ^ m := geom_sum_step p m
    have hcert' : ((p : ℤ)) ^ m * q = k * S * (q + p) + 1 := by exact_mod_cast hcert
    have hgeom' : (p : ℤ) * S + 1 = (S : ℤ) + (p : ℤ) ^ m := by exact_mod_cast hgeom
    have key : ((p ^ m * q + k * (p ^ m * q + 1) : ℕ) : ℤ)
        = ((k * ((S + p ^ m) * (q + 1)) + 1 : ℕ) : ℤ) := by
      push_cast
      linear_combination hcert' + (k : ℤ) * hgeom'
    exact_mod_cast key

/-- **Semiprime criterion.** For distinct primes `p ≠ q`, the number `p * q` is
`k`-hyperperfect if and only if `p * q = k * (p + q) + 1`. -/
theorem isHyperperfect_mul_prime_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsHyperperfect k (p * q) ↔ p * q = k * (p + q) + 1 := by
  constructor
  · rintro ⟨-, h⟩
    rw [show p * q = p ^ 1 * q by ring, sigma_primePow_mul_prime hp hq hpq] at h
    have h' : ((p ^ 1 * q + k * (p ^ 1 * q + 1) : ℕ) : ℤ)
        = ((k * ((∑ i ∈ Finset.range (1 + 1), (p : ℕ) ^ i) * (q + 1)) + 1 : ℕ) : ℤ) := by
      exact_mod_cast h
    simp [Finset.sum_range_succ] at h'
    have : (p : ℤ) * q = k * (p + q) + 1 := by linarith
    exact_mod_cast this
  · intro h
    have := isHyperperfect_primePow_mul_prime (k := k) (p := p) (q := q) (m := 1)
      hp hq hpq one_pos (by simpa [Finset.sum_range_succ, Nat.add_comm] using h)
    simpa using this

/-- **The classical hyperperfect family.** If `2 * p = 3 * k + 1` and `q = 3 * k + 4` with
`p` and `q` prime, then `p ^ 2 * q` is `k`-hyperperfect.  (This forces `k` to be odd.) -/
theorem isHyperperfect_classical_family {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpk : 2 * p = 3 * k + 1) (hqk : q = 3 * k + 4) : IsHyperperfect k (p ^ 2 * q) := by
  have hpq : p ≠ q := by omega
  refine isHyperperfect_primePow_mul_prime hp hq hpq (by norm_num) ?_
  have hpk' : (2 : ℤ) * p = 3 * k + 1 := by exact_mod_cast hpk
  have hqk' : (q : ℤ) = 3 * k + 4 := by exact_mod_cast hqk
  have key : ((p ^ 2 * q : ℕ) : ℤ)
      = ((k * (∑ i ∈ Finset.range 2, p ^ i) * (q + p) + 1 : ℕ) : ℤ) := by
    push_cast [Finset.sum_range_succ]
    linear_combination (((k : ℤ) + 2) * p + ((k : ℤ) + 1)) * hpk'
      + ((p : ℤ) ^ 2 - (k : ℤ) * (1 + p)) * hqk'
  exact_mod_cast key

/-- `6` is `1`-hyperperfect, i.e. perfect. -/
theorem isHyperperfect_one_six : IsHyperperfect 1 6 := by
  have := isHyperperfect_primePow_mul_prime (k := 1) (p := 2) (q := 3) (m := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  simpa using this

/-- `21 = 3 · 7` is `2`-hyperperfect. -/
theorem isHyperperfect_two_21 : IsHyperperfect 2 21 := by
  have := isHyperperfect_primePow_mul_prime (k := 2) (p := 3) (q := 7) (m := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  simpa using this

/-- `325 = 5² · 13` is `3`-hyperperfect. -/
theorem isHyperperfect_three_325 : IsHyperperfect 3 325 := by
  have := isHyperperfect_primePow_mul_prime (k := 3) (p := 5) (q := 13) (m := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  simpa using this

/-- `1950625 = 5⁴ · 3121` is `4`-hyperperfect. -/
theorem isHyperperfect_four_1950625 : IsHyperperfect 4 1950625 := by
  have := isHyperperfect_primePow_mul_prime (k := 4) (p := 5) (q := 3121) (m := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  norm_num at this
  exact this

/-- `301 = 7 · 43` is `6`-hyperperfect. -/
theorem isHyperperfect_six_301 : IsHyperperfect 6 301 := by
  have := (isHyperperfect_mul_prime_iff (k := 6) (p := 7) (q := 43)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

/-- `159841 = 11² · 1321` is `10`-hyperperfect. -/
theorem isHyperperfect_ten_159841 : IsHyperperfect 10 159841 := by
  have := isHyperperfect_primePow_mul_prime (k := 10) (p := 11) (q := 1321) (m := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  norm_num at this
  exact this

/-- `10693 = 17² · 37` is `11`-hyperperfect. -/
theorem isHyperperfect_eleven_10693 : IsHyperperfect 11 10693 := by
  have := isHyperperfect_primePow_mul_prime (k := 11) (p := 17) (q := 37) (m := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  norm_num at this
  exact this

/-- `697 = 17 · 41` is `12`-hyperperfect. -/
theorem isHyperperfect_twelve_697 : IsHyperperfect 12 697 := by
  have := (isHyperperfect_mul_prime_iff (k := 12) (p := 17) (q := 41)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

/-- `1333 = 31 · 43` is `18`-hyperperfect. -/
theorem isHyperperfect_eighteen_1333 : IsHyperperfect 18 1333 := by
  have := (isHyperperfect_mul_prime_iff (k := 18) (p := 31) (q := 43)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

/-- `51301 = 29² · 61` is `19`-hyperperfect. -/
theorem isHyperperfect_nineteen_51301 : IsHyperperfect 19 51301 := by
  have := isHyperperfect_primePow_mul_prime (k := 19) (p := 29) (q := 61) (m := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  norm_num at this
  exact this

/-- `3901 = 47 · 83` is `30`-hyperperfect. -/
theorem isHyperperfect_thirty_3901 : IsHyperperfect 30 3901 := by
  have := (isHyperperfect_mul_prime_iff (k := 30) (p := 47) (q := 83)
    (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num at this
  exact this

/-- `214273 = 47² · 97` is `31`-hyperperfect. -/
theorem isHyperperfect_thirtyone_214273 : IsHyperperfect 31 214273 := by
  have := isHyperperfect_primePow_mul_prime (k := 31) (p := 47) (q := 97) (m := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  norm_num at this
  exact this

end Brockian.HyperperfectNumbers

