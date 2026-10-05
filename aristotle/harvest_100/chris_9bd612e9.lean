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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- The sum-of-divisors function `σ₁`, written directly as a sum over `Nat.divisors`. -/
def sigmaSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A **Zumkeller number** is a positive integer whose set of divisors can be split into two
parts having the same sum. -/
def IsZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d

/-- The divisor sum of a Zumkeller number is even. -/
theorem even_sigmaSum_of_isZumkeller {n : ℕ} (hz : IsZumkeller n) : Even (sigmaSum n) := by
  obtain ⟨-, S, hS, hsum⟩ := hz
  have h := Finset.sum_sdiff (f := fun d : ℕ => d) hS
  refine ⟨∑ d ∈ S, d, ?_⟩
  rw [sigmaSum, ← h, ← hsum]

/-- A Zumkeller number is perfect or abundant: `2n ≤ σ(n)`. -/
theorem two_mul_le_sigmaSum_of_isZumkeller {n : ℕ} (hz : IsZumkeller n) :
    2 * n ≤ sigmaSum n := by
  obtain ⟨hn, S, hS, hsum⟩ := hz
  have h := Finset.sum_sdiff (f := fun d : ℕ => d) hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have hle : n ≤ ∑ d ∈ S, d := by
    by_cases hnS : n ∈ S
    · exact Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) hnS
    · have hmem' : n ∈ n.divisors \ S := Finset.mem_sdiff.mpr ⟨hmem, hnS⟩
      rw [hsum]
      exact Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) hmem'
  have hsplit : sigmaSum n = ∑ d ∈ S, d + ∑ d ∈ S, d := by
    rw [sigmaSum, ← h, ← hsum]
  omega

/-- Geometric sum identity, in a subtraction-free form. -/
theorem geom_sum_mul_self (p k : ℕ) :
    (∑ x ∈ Finset.range (k + 1), p ^ x) * p + 1
      = p ^ (k + 1) + ∑ x ∈ Finset.range (k + 1), p ^ x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ (n := k + 1)]
    ring_nf
    ring_nf at ih
    omega

/-- For a prime `p` with `3 ≤ c ≤ p`, the divisor sum of `p ^ k` is smaller than
`c / (c - 1)` times `p ^ k`. -/
theorem sigmaSum_prime_pow_lt {p c k : ℕ} (hp : p.Prime) (hc : 3 ≤ c) (hcp : c ≤ p) :
    (c - 1) * sigmaSum (p ^ k) < c * p ^ k := by
  have hsum : sigmaSum (p ^ k) = ∑ x ∈ Finset.range (k + 1), p ^ x := by
    rw [sigmaSum, Nat.sum_divisors_prime_pow hp]
  set S := ∑ x ∈ Finset.range (k + 1), p ^ x with hSdef
  have hgeom : S * p + 1 = p ^ (k + 1) + S := geom_sum_mul_self p k
  have hpk : p ^ (k + 1) = p * p ^ k := by ring
  have hP : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
  rw [hsum]
  have h1 : S * p + 1 = p * p ^ k + S := by rw [hgeom, hpk]
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, p = e + 1 := ⟨p - 1, by omega⟩
  set P := (e + 1) ^ k with hPdef
  simp only [Nat.add_sub_cancel]
  have hd2 : 2 ≤ d := by omega
  have hde : d ≤ e := by omega
  have h3 : S * e + 1 = P * e + P := by nlinarith [h1]
  by_contra hcon
  push_neg at hcon
  have h2 : (d + 1) * P * e ≤ d * S * e := Nat.mul_le_mul_right e (by nlinarith [hcon])
  have h4 : d * S * e + d = d * P * e + d * P := by nlinarith [h3]
  have h5 : P * d ≤ P * e := Nat.mul_le_mul_left P hde
  nlinarith [h2, h4, h5, hP, hd2]

/-- An odd positive number with at most two distinct prime factors is deficient. -/
theorem sigmaSum_lt_two_mul_of_card_primeFactors_le_two {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (hcard : n.primeFactors.card ≤ 2) : sigmaSum n < 2 * n := by
  have hn0 : n ≠ 0 := hn.ne'
  have hprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.factorization_prod_pow_eq_self hn0
  have hodd_primes : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hne2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
    have := hpp.two_le
    omega
  interval_cases h : n.primeFactors.card
  · have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp h
    have hn1 : n = 1 := by
      rcases Nat.primeFactors_eq_empty.mp hempty with h0 | h1
      · omega
      · exact h1
    subst hn1
    simp [sigmaSum]
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; simp)
    have hp3 : 3 ≤ p := hodd_primes p (by rw [hp]; simp)
    set a := n.factorization p with ha
    have hnp : n = p ^ a := by
      rw [← hprod, hp, Finset.prod_singleton]
    have hlt := sigmaSum_prime_pow_lt (c := 3) (k := a) hpp (le_refl 3) hp3
    rw [← hnp] at hlt
    omega
  · obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp h
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
    have hp3 : 3 ≤ p := hodd_primes p (by rw [hset]; simp)
    have hq3 : 3 ≤ q := hodd_primes q (by rw [hset]; simp)
    set a := n.factorization p with ha
    set b := n.factorization q with hb
    have hnpq : n = p ^ a * q ^ b := by
      rw [← hprod, hset, Finset.prod_pair hpq]
    have hcop : (p ^ a).Coprime (q ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp hqp).mpr hpq)
    have hmul : sigmaSum n = sigmaSum (p ^ a) * sigmaSum (q ^ b) := by
      rw [hnpq, sigmaSum, sigmaSum, sigmaSum, Nat.Coprime.sum_divisors_mul hcop]
    have main : ∀ u v : ℕ, u.Prime → v.Prime → 3 ≤ u → 5 ≤ v → ∀ i j : ℕ,
        sigmaSum (u ^ i) * sigmaSum (v ^ j) < 2 * (u ^ i * v ^ j) := by
      intro u v hu hv hu3 hv5 i j
      have h1 := sigmaSum_prime_pow_lt (c := 3) (k := i) hu (le_refl 3) hu3
      have h2 := sigmaSum_prime_pow_lt (c := 5) (k := j) hv (by norm_num) hv5
      have hui : 1 ≤ u ^ i := Nat.one_le_pow _ _ hu.pos
      have hvj : 1 ≤ v ^ j := Nat.one_le_pow _ _ hv.pos
      norm_num at h1 h2
      nlinarith [h1, h2, hui, hvj, Nat.zero_le (sigmaSum (u ^ i)),
        Nat.zero_le (sigmaSum (v ^ j))]
    rcases Nat.lt_or_ge p q with hlt | hge
    · have hq5 : 5 ≤ q := by
        have h4 : q ≠ 4 := by rintro rfl; exact absurd hqp (by norm_num)
        omega
      rw [hmul, hnpq]
      exact main p q hpp hqp hp3 hq5 a b
    · have hqlt : q < p := lt_of_le_of_ne hge (Ne.symm hpq)
      have hp5 : 5 ≤ p := by
        have h4 : p ≠ 4 := by rintro rfl; exact absurd hpp (by norm_num)
        omega
      have hmain := main q p hqp hpp hq3 hp5 b a
      rw [hmul, hnpq]
      calc sigmaSum (p ^ a) * sigmaSum (q ^ b)
          = sigmaSum (q ^ b) * sigmaSum (p ^ a) := Nat.mul_comm _ _
        _ < 2 * (q ^ b * p ^ a) := hmain
        _ = 2 * (p ^ a * q ^ b) := by ring

/-- **Odd Zumkeller From 3 Structure.**
Every odd Zumkeller number `n` has an even divisor sum, satisfies `2n ≤ σ(n)` (it is perfect or
abundant), and has at least three distinct prime factors. -/
theorem OddZumkellerFrom3Structure {n : ℕ} (hodd : Odd n) (hz : IsZumkeller n) :
    Even (sigmaSum n) ∧ 2 * n ≤ sigmaSum n ∧ 3 ≤ n.primeFactors.card := by
  refine ⟨even_sigmaSum_of_isZumkeller hz, two_mul_le_sigmaSum_of_isZumkeller hz, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hlt := sigmaSum_lt_two_mul_of_card_primeFactors_le_two hz.1 hodd (by omega)
  have hge := two_mul_le_sigmaSum_of_isZumkeller hz
  omega

/-- `945 = 3 ^ 3 * 5 * 7` is an odd Zumkeller number: its divisors split as `{15, 945}` and the
rest, both summing to `960`. -/
theorem isZumkeller_945 : IsZumkeller 945 := by
  refine ⟨by norm_num, {15, 945}, by decide, by decide⟩

/-- The bound `3` in `OddZumkellerFrom3Structure` is sharp: `945` is an odd Zumkeller number
with exactly three distinct prime factors. -/
theorem three_primeFactors_sharp :
    Odd 945 ∧ IsZumkeller 945 ∧ (945 : ℕ).primeFactors.card = 3 := by
  refine ⟨by decide, isZumkeller_945, ?_⟩
  have h : (945 : ℕ) = 3 ^ 3 * (5 * 7) := by norm_num
  have hpf : (945 : ℕ).primeFactors = {3, 5, 7} := by
    rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow _ (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors (by norm_num)]
    rfl
  rw [hpf]
  rfl

end Brockian.ZumkellerNumbers

