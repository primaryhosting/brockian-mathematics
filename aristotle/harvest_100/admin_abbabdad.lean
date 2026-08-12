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

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* when its set of divisors can be split into
two parts with equal sums, i.e. there is `S ⊆ n.divisors` whose sum is half of `σ₁ n`. -/
def IsZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ⊆ n.divisors, 2 * ∑ d ∈ S, d = ∑ d ∈ n.divisors, d

/-- A Zumkeller number is perfect or abundant. -/
theorem two_mul_le_sigma_of_isZumkeller {n : ℕ} (h : IsZumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hn, S, hS, h2⟩ := h
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have hsplit : ∑ d ∈ n.divisors \ S, d + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  by_cases hnS : n ∈ S
  · have : n ≤ ∑ d ∈ S, d :=
      Finset.single_le_sum (f := fun d => d) (by intros; positivity) hnS
    omega
  · have hmem2 : n ∈ n.divisors \ S := Finset.mem_sdiff.2 ⟨hmem, hnS⟩
    have : n ≤ ∑ d ∈ n.divisors \ S, d :=
      Finset.single_le_sum (f := fun d => d) (by intros; positivity) hmem2
    omega

/-- Prime-power case of the bound `σ₁ n * ∏ (p-1) ≤ n * ∏ p`. -/
theorem sigma_primePow_mul_sub_one_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (∑ d ∈ (p ^ k).divisors, d) * (p - 1) ≤ p ^ k * p := by
  rw [Nat.sum_divisors_prime_pow hp]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, add_mul]
      calc (∑ i ∈ Finset.range (k + 1), (q + 1) ^ i) * q + (q + 1) ^ (k + 1) * q
          ≤ (q + 1) ^ k * (q + 1) + (q + 1) ^ (k + 1) * q := Nat.add_le_add_right ih _
        _ = (q + 1) ^ (k + 1) * (q + 1) := by ring

/-- Key elementary bound: `σ₁ n / n ≤ ∏_{p ∣ n} p / (p-1)`, in a subtraction-free form. -/
theorem sigma_mul_prod_sub_one_le (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1) ≤
      n * ∏ p ∈ n.primeFactors, p := by
  revert hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro _
      rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, Finset.prod_singleton]
      exact sigma_primePow_mul_sub_one_le hp k
  | zero => omega
  | one => simp
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      have hdisj : Disjoint a.primeFactors b.primeFactors := Nat.Coprime.disjoint_primeFactors hab
      rw [hab.primeFactors_mul, Finset.prod_union hdisj, Finset.prod_union hdisj,
        hab.sum_divisors_mul]
      calc ((∑ d ∈ a.divisors, d) * ∑ d ∈ b.divisors, d) *
            ((∏ p ∈ a.primeFactors, (p - 1)) * ∏ p ∈ b.primeFactors, (p - 1))
          = ((∑ d ∈ a.divisors, d) * ∏ p ∈ a.primeFactors, (p - 1)) *
            ((∑ d ∈ b.divisors, d) * ∏ p ∈ b.primeFactors, (p - 1)) := by ring
        _ ≤ (a * ∏ p ∈ a.primeFactors, p) * (b * ∏ p ∈ b.primeFactors, p) :=
            Nat.mul_le_mul (iha ha0) (ihb hb0)
        _ = a * b * ((∏ p ∈ a.primeFactors, p) * ∏ p ∈ b.primeFactors, p) := by ring

/-- For a set of at most two odd primes, `∏ p < 2 * ∏ (p-1)`. -/
theorem prod_lt_two_mul_prod_sub_one {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ Odd p)
    (hcard : s.card ≤ 2) : ∏ p ∈ s, p < 2 * ∏ p ∈ s, (p - 1) := by
  interval_cases h : s.card
  · rw [Finset.card_eq_zero] at h
    subst h
    simp
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.1 h
    obtain ⟨hp, hodd⟩ := hs p (by simp)
    have h3 : 3 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge p 3 with h' | h'
      · interval_cases p
        simp_all [Nat.odd_iff]
      · exact h'
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 h
    obtain ⟨hp, hop⟩ := hs p (by simp)
    obtain ⟨hq, hoq⟩ := hs q (by simp)
    have h3p : 3 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge p 3 with h' | h'
      · interval_cases p
        simp_all [Nat.odd_iff]
      · exact h'
    have h3q : 3 ≤ q := by
      have := hq.two_le
      rcases Nat.lt_or_ge q 3 with h' | h'
      · interval_cases q
        simp_all [Nat.odd_iff]
      · exact h'
    have h5 : 5 ≤ p ∨ 5 ≤ q := by
      rcases Nat.lt_or_ge p 5 with h' | h'
      · rcases Nat.lt_or_ge q 5 with h'' | h''
        · interval_cases p <;> interval_cases q <;> simp_all [Nat.odd_iff]
        · exact Or.inr h''
      · exact Or.inl h'
    rw [Finset.prod_pair hpq, Finset.prod_pair hpq]
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rcases h5 with h5 | h5
    · nlinarith
    · nlinarith

/-- An odd Zumkeller number has at least three distinct prime factors. -/
theorem three_le_card_primeFactors_of_odd_zumkeller {n : ℕ} (hodd : Odd n)
    (h : IsZumkeller n) : 3 ≤ n.primeFactors.card := by
  have hz := two_mul_le_sigma_of_isZumkeller h
  obtain ⟨hn, -⟩ := h
  by_contra hc
  push_neg at hc
  have hcard : n.primeFactors.card ≤ 2 := by omega
  rw [Nat.odd_iff] at hodd
  have hs : ∀ p ∈ n.primeFactors, p.Prime ∧ Odd p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hpp, ?_⟩
    rcases hpp.eq_two_or_odd' with rfl | h'
    · omega
    · exact h'
  have h1 := sigma_mul_prod_sub_one_le n hn
  have h2 := prod_lt_two_mul_prod_sub_one hs hcard
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    obtain ⟨hpp, hop⟩ := hs p hp
    have h2le := hpp.two_le
    have hne : p ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hop
    omega
  have key : (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
      < (2 * n) * ∏ p ∈ n.primeFactors, (p - 1) :=
    calc (∑ d ∈ n.divisors, d) * ∏ p ∈ n.primeFactors, (p - 1)
        ≤ n * ∏ p ∈ n.primeFactors, p := h1
      _ < n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) := by gcongr
      _ = (2 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  have := Nat.lt_of_mul_lt_mul_right key
  omega

/-- Zumkeller numbers are stable under multiplication by a coprime factor. -/
theorem IsZumkeller.mul_coprime {n m : ℕ} (hn : IsZumkeller n) (hm : 0 < m)
    (h : Nat.Coprime n m) : IsZumkeller (n * m) := by
  obtain ⟨hn0, S, hS, hsum⟩ := hn
  refine ⟨Nat.mul_pos hn0 hm, (S ×ˢ m.divisors).image (fun x => x.1 * x.2), ?_, ?_⟩
  · intro k hk
    simp only [Finset.mem_image, Finset.mem_product] at hk
    obtain ⟨⟨d, e⟩, ⟨hd, he⟩, rfl⟩ := hk
    have hd' := Nat.mem_divisors.1 (hS hd)
    have he' := Nat.mem_divisors.1 he
    exact Nat.mem_divisors.2 ⟨mul_dvd_mul hd'.1 he'.1, by positivity⟩
  · have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) (S ×ˢ m.divisors) := by
      rintro ⟨d1, e1⟩ hx1 ⟨d2, e2⟩ hx2 hEq
      simp only [Set.mem_prod, Finset.mem_coe] at hx1 hx2
      have hd1 : d1 ∣ n := (Nat.mem_divisors.1 (hS hx1.1)).1
      have hd2 : d2 ∣ n := (Nat.mem_divisors.1 (hS hx2.1)).1
      have he1 : e1 ∣ m := (Nat.mem_divisors.1 hx1.2).1
      have he2 : e2 ∣ m := (Nat.mem_divisors.1 hx2.2).1
      have hc1 : Nat.Coprime e1 n := Nat.Coprime.coprime_dvd_left he1 h.symm
      have hc2 : Nat.Coprime e2 n := Nat.Coprime.coprime_dvd_left he2 h.symm
      have k1 : Nat.gcd (d1 * e1) n = d1 := by
        rw [Nat.Coprime.gcd_mul_right_cancel _ hc1, Nat.gcd_eq_left hd1]
      have k2 : Nat.gcd (d2 * e2) n = d2 := by
        rw [Nat.Coprime.gcd_mul_right_cancel _ hc2, Nat.gcd_eq_left hd2]
      simp only at hEq
      have hdd : d1 = d2 := by rw [← k1, ← k2, hEq]
      subst hdd
      have hd1pos : 0 < d1 := Nat.pos_of_dvd_of_pos hd1 hn0
      have he : e1 = e2 := Nat.eq_of_mul_eq_mul_left hd1pos hEq
      simp [he]
    rw [Finset.sum_image (by
      intro x hx y hy hxy
      exact hinj (by simpa using hx) (by simpa using hy) hxy)]
    rw [Finset.sum_product]
    have hrw : ∑ d ∈ S, ∑ e ∈ m.divisors, d * e = (∑ d ∈ S, d) * ∑ e ∈ m.divisors, e := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm
    rw [hrw, h.sum_divisors_mul, ← mul_assoc, hsum]

/-- `945 = 3³ · 5 · 7` is a Zumkeller number: its divisors split as
`{15, 945}` against the rest, both halves summing to `960`. -/
theorem isZumkeller_945 : IsZumkeller 945 :=
  ⟨by norm_num, {15, 945}, by decide, by decide⟩

/-- The prime factors of `945` are `3`, `5` and `7`. -/
theorem primeFactors_945 : (945 : ℕ).primeFactors = {3, 5, 7} := by
  have h : (945 : ℕ) = 3 ^ 3 * (5 * 7) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

/-- **Odd Zumkeller From 3 Structure.**
Every odd Zumkeller number has at least three distinct prime factors, and this is sharp:
`945 = 3³·5·7` is an odd Zumkeller number with exactly three distinct prime factors, and
`945 * m` is an odd Zumkeller number for every odd `m` coprime to `945`. -/
theorem OddZumkellerFrom3Structure :
    (∀ n : ℕ, Odd n → IsZumkeller n → 3 ≤ n.primeFactors.card) ∧
      (IsZumkeller 945 ∧ Odd 945 ∧ (945 : ℕ).primeFactors.card = 3) ∧
      (∀ m : ℕ, Odd m → Nat.Coprime 945 m → Odd (945 * m) ∧ IsZumkeller (945 * m)) := by
  refine ⟨fun n hodd h => three_le_card_primeFactors_of_odd_zumkeller hodd h,
    ⟨isZumkeller_945, by decide, by rw [primeFactors_945]; decide⟩, fun m hm hcop => ⟨?_, ?_⟩⟩
  · exact Nat.odd_mul.2 ⟨by decide, hm⟩
  · exact isZumkeller_945.mul_coprime hm.pos hcop

end Brockian.ZumkellerNumbers

