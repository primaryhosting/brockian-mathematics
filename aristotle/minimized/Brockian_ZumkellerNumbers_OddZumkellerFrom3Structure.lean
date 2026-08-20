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

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.ZumkellerNumbers

/-- A natural number `n` is *Zumkeller* if it is positive and its set of divisors can be
split into two parts with equal sums. -/
def Zumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d

/-- Sanity check: `6` is a Zumkeller number, via the split `{1, 2, 3} ∪ {6}`. -/
example : Zumkeller 6 := ⟨by norm_num, {1, 2, 3}, by decide, by decide⟩

/-- Sanity check: `945`, the smallest odd Zumkeller number, is Zumkeller,
via the split `{15, 945} ∪ (rest)`. -/
example : Zumkeller 945 := ⟨by norm_num, {15, 945}, by decide +kernel, by decide +kernel⟩

/-- A Zumkeller number is perfect or abundant: `2 * n ≤ σ n`. -/
theorem two_mul_le_sum_divisors_of_zumkeller {n : ℕ} (h : Zumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hn, S, hS, hsum⟩ := h
  have hsplit : ∑ d ∈ n.divisors \ S, d + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  by_cases hnS : n ∈ S
  · have : n ≤ ∑ d ∈ S, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hnS
    omega
  · have hmem' : n ∈ n.divisors \ S := Finset.mem_sdiff.mpr ⟨hmem, hnS⟩
    have : n ≤ ∑ d ∈ n.divisors \ S, d :=
      Finset.single_le_sum (fun i _ => Nat.zero_le i) hmem'
    omega

/-- Key bound: `(∏ (p-1)) * σ n < (∏ p) * n`, the products being over the prime factors of `n`. -/
theorem prod_sub_one_mul_sum_divisors_lt {n : ℕ} (hn : n ≠ 0) (hne : n.primeFactors.Nonempty) :
    (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      < (∏ p ∈ n.primeFactors, p) * n := by
  have hdiv : ∑ d ∈ n.divisors, d
      = ∏ p ∈ n.primeFactors, ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k :=
    Nat.sum_divisors hn
  have hnprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    Nat.factorization_prod_pow_eq_self hn
  have key : ∀ p ∈ n.primeFactors,
      (p - 1) * (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k)
        < p * p ^ n.factorization p := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hgeom : ∀ m : ℕ, (p - 1) * (∑ k ∈ Finset.range (m + 1), p ^ k) = p ^ (m + 1) - 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [Finset.sum_range_succ, Nat.mul_add, ih]
          have hpm : 1 ≤ p ^ (m + 1) := Nat.one_le_pow _ _ (by omega)
          have hmul : (p - 1) * p ^ (m + 1) = p ^ (m + 1 + 1) - p ^ (m + 1) := by
            rw [Nat.sub_mul, one_mul, ← pow_succ']
          have hmono : p ^ (m + 1) ≤ p ^ (m + 1 + 1) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          rw [hmul]
          omega
    rw [hgeom, ← pow_succ']
    have : 1 ≤ p ^ (n.factorization p + 1) := Nat.one_le_pow _ _ (by omega)
    omega
  calc (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      = ∏ p ∈ n.primeFactors,
          ((p - 1) * ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) := by
        rw [hdiv, ← Finset.prod_mul_distrib]
    _ < ∏ p ∈ n.primeFactors, (p * p ^ n.factorization p) :=
        Finset.prod_lt_prod_of_nonempty
          (fun p hp => by
            have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
            have hs : 0 < ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k := by
              refine Finset.sum_pos (fun k _ => pow_pos (show 0 < p by omega) k) ⟨0, ?_⟩
              exact Finset.mem_range.mpr (by omega)
            have : 0 < p - 1 := by omega
            positivity)
          key hne
    _ = (∏ p ∈ n.primeFactors, p) * n := by
        rw [Finset.prod_mul_distrib, hnprod]

/-- For odd `n` with at most two prime factors, `∏ p ≤ 2 * ∏ (p - 1)`. -/
theorem prod_primeFactors_le {n : ℕ} (hodd : Odd n) (hcard : n.primeFactors.card ≤ 2) :
    (∏ p ∈ n.primeFactors, p) ≤ 2 * ∏ p ∈ n.primeFactors, (p - 1) := by
  have hodd' : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, rfl⟩ := hdvd
      rw [Nat.odd_iff] at hodd
      omega
    have := hprime.two_le
    omega
  interval_cases hc : n.primeFactors.card
  · rw [Finset.card_eq_zero] at hc
    simp [hc]
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hp3 : 3 ≤ p := hodd' p (by simp [hp])
    simp only [hp, Finset.prod_singleton]
    omega
  · obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc
    have hp3 : 3 ≤ p := hodd' p (by simp [hset])
    have hq3 : 3 ≤ q := hodd' q (by simp [hset])
    have hpprime := Nat.prime_of_mem_primeFactors (show p ∈ n.primeFactors by simp [hset])
    have hqprime := Nat.prime_of_mem_primeFactors (show q ∈ n.primeFactors by simp [hset])
    have hp4 : p ≠ 4 := by rintro rfl; norm_num at hpprime
    have hq4 : q ≠ 4 := by rintro rfl; norm_num at hqprime
    -- distinct odd primes, so one of them is `≥ 5`
    have hp5 : 5 ≤ p ∨ 5 ≤ q := by omega
    rw [hset, Finset.prod_pair hpq, Finset.prod_pair hpq]
    rcases hp5 with h5 | h5
    · nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega),
        Nat.sub_add_cancel (show 1 ≤ q by omega)]
    · nlinarith [Nat.sub_add_cancel (show 1 ≤ p by omega),
        Nat.sub_add_cancel (show 1 ≤ q by omega)]

/-- An odd number with at most two distinct prime factors is deficient: `σ n < 2 * n`. -/
theorem sum_divisors_lt_of_card_le_two {n : ℕ} (hn : n ≠ 0) (hodd : Odd n)
    (hcard : n.primeFactors.card ≤ 2) : ∑ d ∈ n.divisors, d < 2 * n := by
  rcases Finset.eq_empty_or_nonempty n.primeFactors with hemp | hne
  · have hone : n = 1 := by
      rcases Nat.primeFactors_eq_empty.mp hemp with h | h <;> omega
    subst hone
    simp
  · have h1 := prod_sub_one_mul_sum_divisors_lt hn hne
    have h2 := prod_primeFactors_le hodd hcard
    have key : (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
        < (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) := by
      calc (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
          < (∏ p ∈ n.primeFactors, p) * n := h1
        _ ≤ (2 * ∏ p ∈ n.primeFactors, (p - 1)) * n := Nat.mul_le_mul_right _ h2
        _ = (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) := by ring
    exact lt_of_mul_lt_mul_left key (Nat.zero_le _)

/-- **Odd Zumkeller From 3 Structure.** Every odd Zumkeller number has at least three
distinct prime factors. -/
theorem OddZumkellerFrom3Structure {n : ℕ} (hodd : Odd n) (h : Zumkeller n) :
    3 ≤ n.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hn : n ≠ 0 := h.1.ne'
  have h1 := two_mul_le_sum_divisors_of_zumkeller h
  have h2 := sum_divisors_lt_of_card_le_two hn hodd (by omega)
  omega

end Brockian.ZumkellerNumbers

