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

A *Zumkeller number* is a positive integer whose divisors can be split into two sets with
equal sums.  Here we prove that an odd Zumkeller number must have at least three distinct
prime factors.

The argument: a Zumkeller number is perfect or abundant (`σ(n) ≥ 2n`), while an odd number
with at most two distinct prime factors `p < q` satisfies
`σ(n)/n < p/(p-1) · q/(q-1) ≤ (3/2)(5/4) < 2`, hence is deficient.
-/

open scoped BigOperators

set_option maxRecDepth 40000

namespace Brockian.ZumkellerNumbers

/-- `n` is a *Zumkeller number* if it is positive and its set of divisors can be split into
two parts having the same sum. -/
def IsZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d

/-- A Zumkeller number is perfect or abundant: `σ(n) ≥ 2n`. -/
theorem two_mul_le_sigma_of_isZumkeller {n : ℕ} (hn : IsZumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hpos, S, hS, hsum⟩ := hn
  have hsplit : ∑ d ∈ n.divisors \ S, d + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hpos.ne'
  by_cases hnS : n ∈ S
  · have : n ≤ ∑ d ∈ S, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hnS
    omega
  · have hnT : n ∈ n.divisors \ S := Finset.mem_sdiff.mpr ⟨hmem, hnS⟩
    have : n ≤ ∑ d ∈ n.divisors \ S, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hnT
    omega

/-- Geometric sum identity in `ℕ`. -/
theorem geom_sum_nat (m k : ℕ) :
    m * (∑ i ∈ Finset.range k, (m + 1) ^ i) + 1 = (m + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, pow_succ]
    nlinarith [ih]

/-- Key bound: `(∏_{p ∣ n} (p-1)) * σ(n) ≤ (∏_{p ∣ n} p) * n`, i.e.
`σ(n)/n ≤ ∏_{p ∣ n} p/(p-1)`. -/
theorem prod_pred_mul_sigma_le : ∀ n : ℕ, 0 < n →
    (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      ≤ (∏ p ∈ n.primeFactors, p) * n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro _
      have hpf : (p ^ k).primeFactors = {p} := Nat.primeFactors_prime_pow hk.ne' hp
      rw [hpf]
      simp only [Finset.prod_singleton]
      rw [Nat.sum_divisors_prime_pow hp (f := fun x => x)]
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
      simp only [Nat.add_sub_cancel]
      have hg := geom_sum_nat m (k + 1)
      calc m * (∑ i ∈ Finset.range (k + 1), (m + 1) ^ i) ≤ (m + 1) ^ (k + 1) := by omega
        _ = (m + 1) * (m + 1) ^ k := by ring
  | zero => omega
  | one => simp
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors,
        Finset.prod_union hab.disjoint_primeFactors, hab.sum_divisors_mul]
      calc ((∏ p ∈ a.primeFactors, (p - 1)) * (∏ p ∈ b.primeFactors, (p - 1))) *
            ((∑ d ∈ a.divisors, d) * (∑ d ∈ b.divisors, d))
          = ((∏ p ∈ a.primeFactors, (p - 1)) * (∑ d ∈ a.divisors, d)) *
            ((∏ p ∈ b.primeFactors, (p - 1)) * (∑ d ∈ b.divisors, d)) := by ring
        _ ≤ ((∏ p ∈ a.primeFactors, p) * a) * ((∏ p ∈ b.primeFactors, p) * b) :=
            Nat.mul_le_mul (iha ha0) (ihb hb0)
        _ = ((∏ p ∈ a.primeFactors, p) * (∏ p ∈ b.primeFactors, p)) * (a * b) := by ring

/-- For an odd number with at most two distinct prime factors, `∏ p < 2 * ∏ (p - 1)`. -/
theorem prod_lt_two_mul_prod_pred {n : ℕ} (hodd : Odd n) (hcard : n.primeFactors.card ≤ 2) :
    (∏ p ∈ n.primeFactors, p) < 2 * ∏ p ∈ n.primeFactors, (p - 1) := by
  have hp3 : ∀ p ∈ n.primeFactors, 3 ≤ p ∧ Odd p := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hpd
      obtain ⟨j, hj⟩ := hodd
      omega
    refine ⟨?_, hpp.odd_of_ne_two hp2⟩
    have := hpp.two_le
    omega
  interval_cases h : n.primeFactors.card
  · rw [Finset.card_eq_zero] at h
    simp [h]
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
    obtain ⟨h3, -⟩ := hp3 p (by rw [hp]; simp)
    rw [hp]
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp h
    obtain ⟨hp3', hpo⟩ := hp3 p (by rw [hs]; simp)
    obtain ⟨hq3', hqo⟩ := hp3 q (by rw [hs]; simp)
    rw [hs, Finset.prod_pair hpq, Finset.prod_pair hpq]
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    obtain ⟨ka, hka⟩ := hpo
    obtain ⟨kb, hkb⟩ := hqo
    have ha2 : 2 ≤ a := by omega
    have hb2 : 2 ≤ b := by omega
    have hne : a ≠ b := by omega
    have hor : 4 ≤ a ∨ 4 ≤ b := by omega
    rcases hor with h4 | h4 <;> nlinarith

/-- An odd number with at most two distinct prime factors is deficient: `σ(n) < 2n`. -/
theorem sigma_lt_two_mul_of_card_le_two {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (hcard : n.primeFactors.card ≤ 2) : (∑ d ∈ n.divisors, d) < 2 * n := by
  have hQpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have hpp := (Nat.mem_primeFactors.mp hp).1
    have := hpp.two_le
    omega
  have hkey := prod_pred_mul_sigma_le n hn
  have hlt := prod_lt_two_mul_prod_pred hodd hcard
  have : (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      < (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) := by
    calc (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
        ≤ (∏ p ∈ n.primeFactors, p) * n := hkey
      _ < (2 * ∏ p ∈ n.primeFactors, (p - 1)) * n := by
          exact Nat.mul_lt_mul_of_lt_of_le hlt (le_refl n) hn
      _ = (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) := by ring
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Odd Zumkeller From 3 Structure.**  Every odd Zumkeller number has at least three
distinct prime factors. -/
theorem OddZumkellerFrom3Structure {n : ℕ} (hodd : Odd n) (hz : IsZumkeller n) :
    3 ≤ n.primeFactors.card := by
  by_contra hcon
  have hcard : n.primeFactors.card ≤ 2 := by omega
  have h1 := two_mul_le_sigma_of_isZumkeller hz
  have h2 := sigma_lt_two_mul_of_card_le_two hz.1 hodd hcard
  omega

/-- `945` is an odd Zumkeller number, witnessing that the hypotheses of
`OddZumkellerFrom3Structure` are satisfiable. -/
theorem isZumkeller_945 : IsZumkeller 945 :=
  ⟨by norm_num, {945, 15}, by decide, by decide⟩

/-- `945 = 3^3 · 5 · 7` has exactly three distinct prime factors, so the bound of
`OddZumkellerFrom3Structure` is sharp. -/
theorem card_primeFactors_945 : (945 : ℕ).primeFactors.card = 3 := by
  have h : (945 : ℕ) = 3 ^ 3 * 5 * 7 := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

end Brockian.ZumkellerNumbers

