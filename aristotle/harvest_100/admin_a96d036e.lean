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
/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators

namespace Brockian
namespace ZumkellerNumbers

/-- A positive natural number `n` is *Zumkeller* if its set of divisors can be split into
two blocks having the same sum. -/
def IsZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d

/-- For a prime power, `σ(p^a) * (p - 1) ≤ p^a * p`. -/
theorem sigma_prime_pow_mul_pred_le (p a : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p ^ a).divisors, d) * (p - 1) ≤ p ^ a * p := by
  rw [Nat.sum_divisors_prime_pow hp]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, add_mul]
    calc (∑ x ∈ Finset.range (a + 1), (q + 1) ^ x) * q + (q + 1) ^ (a + 1) * q
        ≤ (q + 1) ^ a * (q + 1) + (q + 1) ^ (a + 1) * q := by gcongr
      _ = (q + 1) ^ (a + 1) * (q + 1) := by ring

/-- The sum-of-divisors function factors over the prime factorisation. -/
theorem sum_divisors_eq_prod (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, d)
      = ∏ p ∈ n.primeFactors, (∑ d ∈ (p ^ n.factorization p).divisors, d) := by
  have h := ArithmeticFunction.isMultiplicative_sigma (k := 1) |>.multiplicative_factorization _ hn
  simp only [ArithmeticFunction.sigma_one_apply] at h
  rw [h, Finsupp.prod, Nat.support_factorization]

theorem self_eq_prod_primeFactors_pow (n : ℕ) (hn : n ≠ 0) :
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-- The key abundancy bound: `σ(n) * ∏_{p ∣ n} (p - 1) ≤ n * ∏_{p ∣ n} p`. -/
theorem sum_divisors_mul_prod_pred_le (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
      ≤ n * ∏ p ∈ n.primeFactors, p := by
  calc (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
      = ∏ p ∈ n.primeFactors, ((∑ d ∈ (p ^ n.factorization p).divisors, d) * (p - 1)) := by
        rw [sum_divisors_eq_prod n hn, ← Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) :=
        Finset.prod_le_prod' fun p hp =>
          sigma_prime_pow_mul_pred_le p _ (Nat.prime_of_mem_primeFactors hp)
    _ = n * ∏ p ∈ n.primeFactors, p := by
        rw [Finset.prod_mul_distrib, ← self_eq_prod_primeFactors_pow n hn]

/-- Two distinct odd numbers `≥ 3` satisfy `p * q < 2 * ((p - 1) * (q - 1))`. -/
theorem mul_lt_two_mul_pred_mul_pred {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
    p * q < 2 * ((p - 1) * (q - 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = 2 * a + 3 := by
    obtain ⟨k, hk⟩ := hpo; exact ⟨k - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = 2 * b + 3 := by
    obtain ⟨k, hk⟩ := hqo; exact ⟨k - 1, by omega⟩
  have h1 : 1 ≤ a + b := by omega
  rw [show 2 * a + 3 - 1 = 2 * a + 2 from by omega, show 2 * b + 3 - 1 = 2 * b + 2 from by omega]
  nlinarith

/-- A Zumkeller number is abundant-or-perfect: `2 * n ≤ σ(n)`. -/
theorem two_mul_le_sum_divisors {n : ℕ} (hz : IsZumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hpos, S, hS, hsum⟩ := hz
  have hsplit : (∑ d ∈ n.divisors \ S, d) + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hpos.ne'
  have hn : n ≤ ∑ d ∈ S, d := by
    by_cases h : n ∈ S
    · exact Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) h
    · have hmem' : n ∈ n.divisors \ S := Finset.mem_sdiff.2 ⟨hmem, h⟩
      have h2 : n ≤ ∑ d ∈ n.divisors \ S, d := by
        simpa using Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) hmem'
      omega
  omega

/-- **Odd Zumkeller From 3 Structure.**
Every odd Zumkeller number has at least three distinct prime factors.
Consequently no odd prime power, and no product of two odd prime powers, is Zumkeller. -/
theorem OddZumkellerFrom3Structure {n : ℕ} (hodd : Odd n) (hz : IsZumkeller n) :
    3 ≤ n.primeFactors.card := by
  by_contra hcard
  push_neg at hcard
  have hn0 : n ≠ 0 := by rintro rfl; simp at hodd
  -- every prime factor of `n` is odd and at least 3
  have hp3 : ∀ p ∈ n.primeFactors, 3 ≤ p ∧ Odd p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hne2 : p ≠ 2 := by
      rintro rfl
      have := Nat.odd_iff.mp hodd
      omega
    refine ⟨?_, hpp.odd_of_ne_two hne2⟩
    have := hpp.two_le
    omega
  -- the product bound
  have hprodlt : ∏ p ∈ n.primeFactors, p < 2 * ∏ p ∈ n.primeFactors, (p - 1) := by
    interval_cases h : n.primeFactors.card
    · rw [Finset.card_eq_zero] at h
      rw [h]; simp
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h
      have := hp3 p (by rw [hp]; simp)
      rw [hp]; simp; omega
    · obtain ⟨p, q, hne, hpq⟩ := Finset.card_eq_two.1 h
      have h1 := hp3 p (by rw [hpq]; simp)
      have h2 := hp3 q (by rw [hpq]; simp)
      rw [hpq, Finset.prod_pair hne, Finset.prod_pair hne]
      exact mul_lt_two_mul_pred_mul_pred h1.1 h2.1 h1.2 h2.2 hne
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_pos (fun p hp => by have := hp3 p hp; omega)
  have hkey := sum_divisors_mul_prod_pred_le n hn0
  have habund := two_mul_le_sum_divisors hz
  have hlt : (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
      < (2 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
        ≤ n * ∏ p ∈ n.primeFactors, p := hkey
      _ < n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) := by
          have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          exact (Nat.mul_lt_mul_left hnpos).mpr hprodlt
      _ = (2 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact absurd hlt (not_lt.2 (Nat.mul_le_mul_right _ habund))

/-- No power of an odd prime is a Zumkeller number. -/
theorem not_isZumkeller_odd_prime_pow {p a : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    ¬ IsZumkeller (p ^ a) := by
  intro hz
  have hodd : Odd (p ^ a) := hpodd.pow
  have h3 := OddZumkellerFrom3Structure hodd hz
  have hsub : (p ^ a).primeFactors ⊆ {p} := by
    intro q hq
    simp only [Finset.mem_singleton]
    exact (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq) hp).1
      ((Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq))
  have := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

end ZumkellerNumbers
end Brockian

