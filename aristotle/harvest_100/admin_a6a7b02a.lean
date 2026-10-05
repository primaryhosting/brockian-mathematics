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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

open Finset

/-- A positive natural number `n` is *Zumkeller* if its set of divisors can be split into
two blocks with equal sums. -/
def Zumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d

/-- A Zumkeller number is at least perfect: `σ(n) ≥ 2n`. -/
theorem two_mul_le_sigma_of_zumkeller {n : ℕ} (hz : Zumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hn, S, hS, hsum⟩ := hz
  have hsplit : ∑ d ∈ n.divisors \ S, d + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have key : n ≤ ∑ d ∈ S, d := by
    by_cases h : n ∈ S
    · exact Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) h
    · have hmem' : n ∈ n.divisors \ S := Finset.mem_sdiff.mpr ⟨hmem, h⟩
      have := Finset.single_le_sum (f := fun d => (d : ℕ)) (fun i _ => Nat.zero_le i) hmem'
      simp only at this
      omega
  omega

/-- Geometric-sum identity for the divisor sum of a prime power:
`(1 + p + ⋯ + p ^ a) * (p - 1) + 1 = p ^ (a + 1)`. -/
theorem sum_divisors_prime_pow_mul_pred (p a : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p ^ a).divisors, d) * (p - 1) + 1 = p ^ (a + 1) := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  induction a with
  | zero => simp; omega
  | succ k ih =>
    rw [Nat.sum_divisors_prime_pow hp] at *
    rw [Finset.sum_range_succ, add_mul]
    have h2 : p ^ (k + 1) * (p - 1) + p ^ (k + 1) = p ^ (k + 1) * p := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h3 : p ^ (k + 1 + 1) = p ^ (k + 1) * p := pow_succ p (k + 1)
    omega

/-- Divisor-sum bound for a prime power: `σ(p ^ a) * (p - 1) ≤ p ^ a * p`. -/
theorem sum_divisors_prime_pow_le (p a : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p ^ a).divisors, d) * (p - 1) ≤ p ^ a * p := by
  have h1 := sum_divisors_prime_pow_mul_pred p a hp
  have h2 : p ^ (a + 1) = p ^ a * p := pow_succ p a
  omega

/-- An odd number with at most two distinct prime factors is deficient: `σ(n) < 2n`. -/
theorem sigma_lt_two_mul_of_odd_of_card_primeFactors_le_two {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (hcard : n.primeFactors.card ≤ 2) : (∑ d ∈ n.divisors, d) < 2 * n := by
  have hn0 : n ≠ 0 := hn.ne'
  have hfac : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have := Nat.factorization_prod_pow_eq_self hn0
    rwa [Finsupp.prod, Nat.support_factorization] at this
  have hodd3 : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have h2 := hpp.two_le
    rcases hpp.eq_two_or_odd with rfl | hp2
    · exfalso
      rw [Nat.odd_iff] at hodd
      omega
    · omega
  interval_cases hc : n.primeFactors.card
  · -- no prime factors: `n = 1`
    have hemp : n.primeFactors = ∅ := Finset.card_eq_zero.mp hc
    have hn1 : n = 1 := by
      rcases Nat.primeFactors_eq_empty.mp hemp with h0 | h1
      · omega
      · exact h1
    subst hn1
    simp
  · -- one prime factor: `n = p ^ a` with `p ≥ 3`
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; simp)
    have hp3 : 3 ≤ p := hodd3 p (by rw [hp]; simp)
    obtain ⟨a, ha⟩ : ∃ a, p ^ a = n := by
      refine ⟨n.factorization p, ?_⟩
      conv_rhs => rw [← hfac]
      rw [hp, Finset.prod_singleton]
    have hle := sum_divisors_prime_pow_le p a hpp
    rw [ha] at hle
    have h1 : n * p < 2 * n * (p - 1) := by
      have hlt : p < 2 * (p - 1) := by omega
      calc n * p < n * (2 * (p - 1)) := (Nat.mul_lt_mul_left hn).mpr hlt
        _ = 2 * n * (p - 1) := by ring
    exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hle h1)
  · -- two prime factors: `n = p ^ a * q ^ b` with `3 ≤ p, q` distinct
    obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
    have hp3 : 3 ≤ p := hodd3 p (by rw [hset]; simp)
    have hq3 : 3 ≤ q := hodd3 q (by rw [hset]; simp)
    obtain ⟨a, b, hab⟩ : ∃ a b, p ^ a * q ^ b = n := by
      refine ⟨n.factorization p, n.factorization q, ?_⟩
      conv_rhs => rw [← hfac]
      rw [hset, Finset.prod_pair hpq]
    have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hpp hqp).mpr hpq)
    have hsig : ∑ d ∈ n.divisors, d
        = (∑ d ∈ (p ^ a).divisors, d) * ∑ d ∈ (q ^ b).divisors, d := by
      rw [← hab, hcop.sum_divisors_mul]
    have h1 := sum_divisors_prime_pow_le p a hpp
    have h2 := sum_divisors_prime_pow_le q b hqp
    have hkey : (∑ d ∈ n.divisors, d) * ((p - 1) * (q - 1)) ≤ n * (p * q) := by
      rw [hsig, ← hab]
      calc (∑ d ∈ (p ^ a).divisors, d) * (∑ d ∈ (q ^ b).divisors, d) * ((p - 1) * (q - 1))
          = ((∑ d ∈ (p ^ a).divisors, d) * (p - 1)) * ((∑ d ∈ (q ^ b).divisors, d) * (q - 1)) := by
            ring
        _ ≤ (p ^ a * p) * (q ^ b * q) := Nat.mul_le_mul h1 h2
        _ = p ^ a * q ^ b * (p * q) := by ring
    have hpq5 : p * q < 2 * ((p - 1) * (q - 1)) := by
      have hodd5 : 5 ≤ p ∨ 5 ≤ q := by
        by_contra hcon
        push_neg at hcon
        have hp4 : p ≤ 4 := by omega
        have hq4 : q ≤ 4 := by omega
        have hpe : p = 3 := by interval_cases p <;> first | rfl | exact absurd hpp (by norm_num)
        have hqe : q = 3 := by interval_cases q <;> first | rfl | exact absurd hqp (by norm_num)
        exact hpq (hpe.trans hqe.symm)
      obtain ⟨P, rfl⟩ : ∃ P, p = P + 1 := ⟨p - 1, by omega⟩
      obtain ⟨Q, rfl⟩ : ∃ Q, q = Q + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rcases hodd5 with h5 | h5 <;> nlinarith
    have hlt : n * (p * q) < 2 * n * ((p - 1) * (q - 1)) := by
      calc n * (p * q) < n * (2 * ((p - 1) * (q - 1))) := (Nat.mul_lt_mul_left hn).mpr hpq5
        _ = 2 * n * ((p - 1) * (q - 1)) := by ring
    exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hkey hlt)

/-- **Odd Zumkeller From 3 Structure.**  Every odd Zumkeller number has at least three
distinct prime factors. -/
theorem OddZumkellerFrom3Structure {n : ℕ} (hodd : Odd n) (hz : Zumkeller n) :
    3 ≤ n.primeFactors.card := by
  by_contra h
  have hcard : n.primeFactors.card ≤ 2 := by omega
  have h1 := sigma_lt_two_mul_of_odd_of_card_primeFactors_le_two hz.1 hodd hcard
  have h2 := two_mul_le_sigma_of_zumkeller hz
  omega

/-- The bound is sharp: `945 = 3 ^ 3 · 5 · 7` is an odd Zumkeller number with exactly three
distinct prime factors (the divisor blocks are `{15, 945}` and its complement, each of sum
`960 = σ(945) / 2`). -/
theorem zumkeller_945 : Zumkeller 945 ∧ Odd 945 ∧ (945 : ℕ).primeFactors.card = 3 := by
  refine ⟨⟨by norm_num, {945, 15}, by decide, by decide⟩, by decide, ?_⟩
  have h : (945 : ℕ) = 3 ^ 3 * (5 * 7) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  decide

end Brockian.ZumkellerNumbers

