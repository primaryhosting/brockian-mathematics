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

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Finset

namespace Brockian.ZumkellerNumbers

/-- A natural number `n` is a *Zumkeller number* if its set of divisors can be split into two
parts of equal sum, i.e. there is a set `S` of divisors of `n` whose sum is half of `σ(n)`. -/
def IsZumkeller (n : ℕ) : Prop :=
  ∃ S ⊆ n.divisors, 2 * ∑ d ∈ S, d = ∑ d ∈ n.divisors, d

/-- The sum-of-divisors function is multiplicative. -/
lemma sum_divisors_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    ∑ d ∈ (m * n).divisors, d = (∑ d ∈ m.divisors, d) * ∑ d ∈ n.divisors, d := by
  have := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h
  simpa [ArithmeticFunction.sigma_one_apply] using this

/-- Multiplying a Zumkeller number by a coprime factor yields a Zumkeller number. -/
lemma IsZumkeller.mul_coprime {n m : ℕ} (hn : IsZumkeller n) (h : Nat.Coprime n m) :
    IsZumkeller (n * m) := by
  obtain ⟨S, hS, hsum⟩ := hn
  have hinj : ∀ p ∈ S ×ˢ m.divisors, ∀ q ∈ S ×ˢ m.divisors,
      p.1 * p.2 = q.1 * q.2 → p = q := by
    rintro ⟨a, e⟩ hp ⟨a', e'⟩ hq hpq
    simp only [Finset.mem_product] at hp hq
    have ha : a ∣ n := (Nat.mem_divisors.1 (hS hp.1)).1
    have ha' : a' ∣ n := (Nat.mem_divisors.1 (hS hq.1)).1
    have he : e ∣ m := (Nat.mem_divisors.1 hp.2).1
    have he' : e' ∣ m := (Nat.mem_divisors.1 hq.2).1
    have hcen : Nat.Coprime e n := ((h.coprime_dvd_right he).symm)
    have hce'n : Nat.Coprime e' n := ((h.coprime_dvd_right he').symm)
    have h1 : Nat.gcd (a * e) n = a := by
      rw [Nat.Coprime.gcd_mul_right_cancel _ hcen]
      exact Nat.gcd_eq_left ha
    have h2 : Nat.gcd (a' * e') n = a' := by
      rw [Nat.Coprime.gcd_mul_right_cancel _ hce'n]
      exact Nat.gcd_eq_left ha'
    have haa : a = a' := by rw [← h1, ← h2, hpq]
    subst haa
    have hane : a ≠ 0 := by
      rintro rfl
      have := Nat.pos_of_mem_divisors (hS hp.1)
      omega
    have : e = e' := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hane) hpq
    simp [this]
  refine ⟨(S ×ˢ m.divisors).image (fun p => p.1 * p.2), ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_product] at hx
    obtain ⟨⟨a, e⟩, ⟨ha, he⟩, rfl⟩ := hx
    have han := Nat.mem_divisors.1 (hS ha)
    have hem := Nat.mem_divisors.1 he
    exact Nat.mem_divisors.2 ⟨mul_dvd_mul han.1 hem.1, Nat.mul_ne_zero han.2 hem.2⟩
  · rw [Finset.sum_image hinj, Finset.sum_product]
    have : ∑ x ∈ S, ∑ y ∈ m.divisors, x * y
        = (∑ x ∈ S, x) * ∑ y ∈ m.divisors, y := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    rw [this, ← mul_assoc, hsum, sum_divisors_mul_of_coprime h]

/-- If the divisors of `N` split as the divisors of `b` together with `k` times the divisors of
`n`, and both `b` and `n` are Zumkeller, then so is `N`. -/
lemma zumkeller_of_split {N b n k : ℕ} (hk : k ≠ 0) (hb : IsZumkeller b) (hn : IsZumkeller n)
    (hdisj : Disjoint b.divisors (n.divisors.image (fun d => k * d)))
    (hsplit : N.divisors = b.divisors ∪ n.divisors.image (fun d => k * d)) :
    IsZumkeller N := by
  obtain ⟨A, hA, hAsum⟩ := hb
  obtain ⟨B, hB, hBsum⟩ := hn
  have himg : Finset.image (fun d => k * d) B ⊆ Finset.image (fun d => k * d) n.divisors :=
    Finset.image_subset_image hB
  have himgsum : ∀ T : Finset ℕ, ∑ d ∈ T.image (fun d => k * d), d = k * ∑ d ∈ T, d := by
    intro T
    rw [Finset.sum_image (fun x _ y _ hxy =>
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) hxy), Finset.mul_sum]
  have hdA : Disjoint A (Finset.image (fun d => k * d) B) := hdisj.mono hA himg
  refine ⟨A ∪ Finset.image (fun d => k * d) B, ?_, ?_⟩
  · rw [hsplit]; exact Finset.union_subset_union hA himg
  · rw [Finset.sum_union hdA, hsplit, Finset.sum_union hdisj, himgsum, himgsum,
      Nat.mul_add, hAsum]
    have h2 : 2 * (k * ∑ d ∈ B, d) = k * ∑ d ∈ n.divisors, d := by rw [← hBsum]; ring
    omega

lemma divisors_three_split (a : ℕ) :
    ((3:ℕ) ^ (a + 4) * 35).divisors
      = (945 : ℕ).divisors ∪ (((3:ℕ) ^ a * 35).divisors.image (fun d => 81 * d)) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨hx, -⟩
    rw [Nat.dvd_mul] at hx
    obtain ⟨y, z, hy, hz, rfl⟩ := hx
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hy
    rcases le_or_gt i 3 with h | h
    · left
      refine ⟨?_, by norm_num⟩
      have h1 : (3:ℕ) ^ i * z ∣ 3 ^ 3 * 35 := mul_dvd_mul (pow_dvd_pow 3 h) hz
      simpa using h1
    · right
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 4 := ⟨i - 4, by omega⟩
      refine ⟨3 ^ j * z, ⟨mul_dvd_mul (pow_dvd_pow 3 (by omega)) hz, by positivity⟩, by ring⟩
  · rintro (⟨hx, -⟩ | ⟨y, ⟨hy, -⟩, rfl⟩)
    · refine ⟨hx.trans ?_, by positivity⟩
      have h945 : (945 : ℕ) = 3 ^ 3 * 35 := by norm_num
      rw [h945]
      exact mul_dvd_mul (pow_dvd_pow 3 (by omega)) dvd_rfl
    · refine ⟨?_, by positivity⟩
      have h81 : (81 : ℕ) * (3 ^ a * 35) = 3 ^ (a + 4) * 35 := by ring
      calc 81 * y ∣ 81 * (3 ^ a * 35) := mul_dvd_mul_left _ hy
        _ = 3 ^ (a + 4) * 35 := h81

lemma disjoint_three_split (a : ℕ) :
    Disjoint (945 : ℕ).divisors (((3:ℕ) ^ a * 35).divisors.image (fun d => 81 * d)) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  simp only [Finset.mem_image] at hx'
  obtain ⟨y, -, rfl⟩ := hx'
  have h1 : (81 : ℕ) ∣ 945 := dvd_trans ⟨y, rfl⟩ (Nat.mem_divisors.1 hx).1
  norm_num at h1

lemma zumkeller_945 : IsZumkeller 945 := ⟨{15, 945}, by decide, by decide⟩

lemma zumkeller_2835 : IsZumkeller 2835 := ⟨{1, 5, 63, 2835}, by decide, by decide⟩

lemma zumkeller_8505 : IsZumkeller 8505 := ⟨{7, 35, 189, 8505}, by decide, by decide⟩

lemma zumkeller_25515 : IsZumkeller 25515 := ⟨{15, 135, 567, 25515}, by decide, by decide⟩

/-- For every exponent `a ≥ 3`, the number `3 ^ a * 5 * 7` is a Zumkeller number. -/
lemma zumkeller_three_pow_mul_35 (a : ℕ) : 3 ≤ a → IsZumkeller (3 ^ a * 35) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha
    rcases le_or_gt a 6 with h | h
    · interval_cases a
      · simpa using zumkeller_945
      · simpa using zumkeller_2835
      · simpa using zumkeller_8505
      · simpa using zumkeller_25515
    · obtain ⟨j, rfl⟩ : ∃ j, a = j + 4 := ⟨a - 4, by omega⟩
      exact zumkeller_of_split (by norm_num) zumkeller_945 (ih j (by omega) (by omega))
        (disjoint_three_split j) (divisors_three_split j)

/-- **Odd Zumkeller numbers from the `3`-structure `3 ^ a * 5 * 7`.**
For every exponent `a ≥ 3` and every odd `m` that is not divisible by `3`, `5` or `7`, the
number `3 ^ a * 5 * 7 * m` is an odd Zumkeller number. -/
theorem OddZumkellerFrom3Structure (a m : ℕ) (ha : 3 ≤ a) (hm : Odd m)
    (h3 : ¬ (3 ∣ m)) (h5 : ¬ (5 ∣ m)) (h7 : ¬ (7 ∣ m)) :
    Odd (3 ^ a * 5 * 7 * m) ∧ IsZumkeller (3 ^ a * 5 * 7 * m) := by
  have hcop : Nat.Coprime (3 ^ a * 35) m := by
    have c3 : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    have c5 : Nat.Coprime 5 m := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5
    have c7 : Nat.Coprime 7 m := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h7
    have c35 : Nat.Coprime 35 m := by
      have h35 : (35 : ℕ) = 5 * 7 := by norm_num
      rw [h35]
      exact Nat.Coprime.mul_left c5 c7
    exact Nat.Coprime.mul_left (c3.pow_left a) c35
  have heq : 3 ^ a * 5 * 7 * m = (3 ^ a * 35) * m := by ring
  constructor
  · rw [heq, Nat.odd_mul, Nat.odd_mul]
    exact ⟨⟨Odd.pow (by decide), by decide⟩, hm⟩
  · rw [heq]
    exact (zumkeller_three_pow_mul_35 a ha).mul_coprime hcop

/-- There are infinitely many odd Zumkeller numbers. -/
theorem infinite_odd_zumkeller : {n : ℕ | Odd n ∧ IsZumkeller n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun a : ℕ => 3 ^ (a + 3) * 5 * 7 * 1) ?_ ?_
  · intro x y hxy
    simp only [mul_one] at hxy
    have h1 := Nat.eq_of_mul_eq_mul_right (show 0 < 7 by norm_num) hxy
    have h2 := Nat.eq_of_mul_eq_mul_right (show 0 < 5 by norm_num) h1
    have h3 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2
    omega
  · intro a
    exact OddZumkellerFrom3Structure (a + 3) 1 (by omega) (by decide) (by decide) (by decide)
      (by decide)

end Brockian.ZumkellerNumbers

