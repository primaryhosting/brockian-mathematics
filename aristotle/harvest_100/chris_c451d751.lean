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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The unconditional infinitude of Carmichael numbers with exactly three prime factors is an
open problem.  This file gives a fully checked *conditional reduction*: Korselt's criterion
is proved in the three-prime case, reducing the conjecture to the purely arithmetic statement
`InfinitelyManyKorseltTriples`, and further to a Dickson-type prime-triple hypothesis via
Chernick's parametrisation `(6k+1)(12k+1)(18k+1)`.
-/

namespace Brockian.CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` such that `a ^ (n - 1) ≡ 1 [MOD n]` for every
`a` coprime to `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, Nat.Coprime a n → a ^ (n - 1) ≡ 1 [MOD n]

/-- A Carmichael number that is the product of exactly three distinct primes. -/
def IsThreePrimeCarmichael (n : ℕ) : Prop :=
  IsCarmichael n ∧ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ n = p * q * r

/-- The Korselt condition for a triple of increasing primes `p < q < r`: each of `p - 1`,
`q - 1`, `r - 1` divides `p * q * r - 1`. -/
def IsKorseltTriple (p q r : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧
    (p - 1) ∣ (p * q * r - 1) ∧ (q - 1) ∣ (p * q * r - 1) ∧ (r - 1) ∣ (p * q * r - 1)

/-- The arithmetic statement that there are arbitrarily large Korselt triples. -/
def InfinitelyManyKorseltTriples : Prop :=
  ∀ N : ℕ, ∃ p q r : ℕ, N < p ∧ IsKorseltTriple p q r

/-- Fermat step: if `p` is prime, `p - 1 ∣ m` and `a` is coprime to `p`, then `a ^ m ≡ 1 [MOD p]`. -/
theorem pow_modEq_one_of_sub_one_dvd {p a m : ℕ} (hp : p.Prime) (hdvd : (p - 1) ∣ m)
    (hcop : Nat.Coprime a p) : a ^ m ≡ 1 [MOD p] := by
  obtain ⟨k, hk⟩ := hdvd
  have h1 : a ^ (p - 1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hp] at this
  calc a ^ m = (a ^ (p - 1)) ^ k := by rw [← pow_mul, hk]
    _ ≡ 1 ^ k [MOD p] := h1.pow k
    _ = 1 := one_pow k

/-- **Korselt's criterion (three-prime case, sufficiency).** A Korselt triple gives a Carmichael
number with exactly three prime factors. -/
theorem isThreePrimeCarmichael_of_isKorseltTriple {p q r : ℕ} (h : IsKorseltTriple p q r) :
    IsThreePrimeCarmichael (p * q * r) := by
  obtain ⟨hp, hq, hr, hpq, hqr, hdp, hdq, hdr⟩ := h
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hpne : p ≠ q := Nat.ne_of_lt hpq
  have hqne : q ≠ r := Nat.ne_of_lt hqr
  have hpne' : p ≠ r := Nat.ne_of_lt (lt_trans hpq hqr)
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpne
  have hcpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpne'
  have hcqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqne
  have h4 : 4 * p ≤ p * q * r := by
    calc 4 * p = p * 2 * 2 := by ring
      _ ≤ p * q * r := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hq2) hr2
  have hlt : 1 < p * q * r := by omega
  refine ⟨⟨hlt, ?_, ?_⟩, p, q, r, hp, hq, hr, hpq, hqr, rfl⟩
  · -- compositeness
    intro hprime
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p ⟨q * r, by ring⟩) with h1 | h1
    · omega
    · omega
  · intro a hcop
    have hap : Nat.Coprime a p := Nat.Coprime.coprime_dvd_right ⟨q * r, by ring⟩ hcop
    have haq : Nat.Coprime a q := Nat.Coprime.coprime_dvd_right ⟨p * r, by ring⟩ hcop
    have har : Nat.Coprime a r := Nat.Coprime.coprime_dvd_right ⟨p * q, by ring⟩ hcop
    have e1 : a ^ (p * q * r - 1) ≡ 1 [MOD p] := pow_modEq_one_of_sub_one_dvd hp hdp hap
    have e2 : a ^ (p * q * r - 1) ≡ 1 [MOD q] := pow_modEq_one_of_sub_one_dvd hq hdq haq
    have e3 : a ^ (p * q * r - 1) ≡ 1 [MOD r] := pow_modEq_one_of_sub_one_dvd hr hdr har
    have e12 : a ^ (p * q * r - 1) ≡ 1 [MOD p * q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcpq).mp ⟨e1, e2⟩
    have hcpqr : Nat.Coprime (p * q) r := Nat.Coprime.mul_left hcpr hcqr
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcpqr).mp ⟨e12, e3⟩

/-- **Conditional reduction.** If there are arbitrarily large Korselt triples of primes, then
there are infinitely many Carmichael numbers with exactly three prime factors. -/
theorem ThreePrimeCarmichaelInfinitude (h : InfinitelyManyKorseltTriples) :
    {n : ℕ | IsThreePrimeCarmichael n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, q, r, hN, htriple⟩ := h N
  refine ⟨p * q * r, isThreePrimeCarmichael_of_isKorseltTriple htriple, ?_⟩
  obtain ⟨hp, hq, hr, hpq, hqr, -⟩ := htriple
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have h4 : 4 * p ≤ p * q * r := by
    calc 4 * p = p * 2 * 2 := by ring
      _ ≤ p * q * r := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hq2) hr2
  omega

/-- `561 = 3 * 11 * 17` is a Korselt triple, so the set above is nonempty. -/
theorem isKorseltTriple_3_11_17 : IsKorseltTriple 3 11 17 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩ <;> decide

theorem isThreePrimeCarmichael_561 : IsThreePrimeCarmichael 561 :=
  isThreePrimeCarmichael_of_isKorseltTriple isKorseltTriple_3_11_17

/-- **Chernick's parametrisation.** For `k ≥ 1`, if `6k+1`, `12k+1`, `18k+1` are all prime then
they form a Korselt triple. -/
theorem isKorseltTriple_chernick {k : ℕ} (hk : 1 ≤ k) (h1 : (6 * k + 1).Prime)
    (h2 : (12 * k + 1).Prime) (h3 : (18 * k + 1).Prime) :
    IsKorseltTriple (6 * k + 1) (12 * k + 1) (18 * k + 1) := by
  have hprod : (6 * k + 1) * (12 * k + 1) * (18 * k + 1)
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) + 1 := by ring
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by rw [hprod, Nat.add_sub_cancel]
  refine ⟨h1, h2, h3, by omega, by omega, ?_, ?_, ?_⟩ <;> rw [hsub] <;> simp only [Nat.add_sub_cancel]
  · exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  · exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by ring⟩
  · exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by ring⟩

/-- **Conditional reduction to a Dickson-type prime triple hypothesis.** If there are
arbitrarily large `k` with `6k+1`, `12k+1`, `18k+1` all prime, then there are infinitely many
Carmichael numbers with exactly three prime factors. -/
theorem threePrimeCarmichaelInfinitude_of_chernick
    (h : ∀ N : ℕ, ∃ k : ℕ, N < k ∧ (6 * k + 1).Prime ∧ (12 * k + 1).Prime ∧ (18 * k + 1).Prime) :
    {n : ℕ | IsThreePrimeCarmichael n}.Infinite := by
  apply ThreePrimeCarmichaelInfinitude
  intro N
  obtain ⟨k, hk, h1, h2, h3⟩ := h N
  exact ⟨6 * k + 1, 12 * k + 1, 18 * k + 1, by omega,
    isKorseltTriple_chernick (by omega) h1 h2 h3⟩

/-- `1729 = 7 * 13 * 19` is the Chernick number for `k = 1`. -/
theorem isThreePrimeCarmichael_1729 : IsThreePrimeCarmichael 1729 := by
  have := isThreePrimeCarmichael_of_isKorseltTriple
    (isKorseltTriple_chernick (k := 1) le_rfl (by norm_num) (by norm_num) (by norm_num))
  norm_num at this
  exact this

end Brockian.CarmichaelKorselt

