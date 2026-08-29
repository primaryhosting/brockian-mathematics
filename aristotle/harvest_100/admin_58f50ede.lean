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

open scoped BigOperators

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* if its set of divisors can be split into
two parts with equal sums, i.e. there is a set `A` of divisors of `n` whose sum is exactly
half of `σ(n)`. -/
def IsZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ A ⊆ n.divisors, 2 * ∑ d ∈ A, d = ∑ d ∈ n.divisors, d

/-- Multiplying a Zumkeller number by a coprime factor yields a Zumkeller number. -/
theorem zumkeller_mul_of_coprime {n k : ℕ} (hn : IsZumkeller n) (hk : 0 < k)
    (h : Nat.Coprime n k) : IsZumkeller (n * k) := by
  obtain ⟨hnpos, A, hA, hsum⟩ := hn
  have hinj : ∀ p ∈ A ×ˢ k.divisors, ∀ q ∈ A ×ˢ k.divisors,
      p.1 * p.2 = q.1 * q.2 → p = q := by
    rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq heq
    simp only [Finset.mem_product] at hp hq
    have hp1 : p1 ∣ n := (Nat.mem_divisors.mp (hA hp.1)).1
    have hq1 : q1 ∣ n := (Nat.mem_divisors.mp (hA hq.1)).1
    have hp2 : p2 ∣ k := (Nat.mem_divisors.mp hp.2).1
    have hq2 : q2 ∣ k := (Nat.mem_divisors.mp hq.2).1
    have hc1 : Nat.Coprime p1 q2 := (Nat.Coprime.coprime_dvd_left hp1 h).coprime_dvd_right hq2
    have hc2 : Nat.Coprime q1 p2 := (Nat.Coprime.coprime_dvd_left hq1 h).coprime_dvd_right hp2
    simp only at heq
    have h1 : p1 ∣ q1 := hc1.dvd_of_dvd_mul_right ⟨p2, heq.symm⟩
    have h2 : q1 ∣ p1 := hc2.dvd_of_dvd_mul_right ⟨q2, heq⟩
    have hEq1 : p1 = q1 := Nat.dvd_antisymm h1 h2
    subst hEq1
    have hp1pos : 0 < p1 := Nat.pos_of_dvd_of_pos hp1 hnpos
    have h3 : p2 = q2 := by
      have h4 := heq
      rw [Nat.mul_left_cancel_iff hp1pos] at h4
      exact h4
    simp [h3]
  refine ⟨Nat.mul_pos hnpos hk, (A ×ˢ k.divisors).image (fun p => p.1 * p.2), ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_product] at hx
    obtain ⟨⟨p1, p2⟩, hp, rfl⟩ := hx
    rw [Nat.mem_divisors]
    exact ⟨mul_dvd_mul (Nat.mem_divisors.mp (hA hp.1)).1 (Nat.mem_divisors.mp hp.2).1,
      Nat.mul_ne_zero hnpos.ne' hk.ne'⟩
  · rw [Finset.sum_image hinj, Finset.sum_product]
    have h4 : ∑ x ∈ A, ∑ y ∈ k.divisors, x * y = (∑ x ∈ A, x) * ∑ y ∈ k.divisors, y := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
    rw [h4, ← mul_assoc, hsum, Nat.Coprime.sum_divisors_mul h]

/-- Twice the geometric sum of powers of `3`. -/
lemma two_mul_geom_sum (n : ℕ) : 2 * ∑ i ∈ Finset.range n, (3 : ℤ) ^ i = 3 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

/-- The sum of the divisors of `3 ^ b * 35` equals `24 * (3 ^ (b + 1) - 1)`. -/
lemma sum_divisors_three_pow_mul_35 (b : ℕ) :
    (∑ d ∈ (3 ^ b * 35 : ℕ).divisors, (d : ℤ)) = 24 * (3 ^ (b + 1) - 1) := by
  have hcop : Nat.Coprime (3 ^ b) 35 := Nat.Coprime.pow_left _ (by decide)
  have h1 : ∑ d ∈ (3 ^ b * 35 : ℕ).divisors, d
      = (∑ d ∈ (3 ^ b : ℕ).divisors, d) * ∑ d ∈ (35 : ℕ).divisors, d :=
    Nat.Coprime.sum_divisors_mul hcop
  have h2 : ∑ d ∈ (35 : ℕ).divisors, d = 48 := by decide
  have h3 : ∑ d ∈ (3 ^ b : ℕ).divisors, d = ∑ i ∈ Finset.range (b + 1), 3 ^ i :=
    Nat.sum_divisors_prime_pow (by norm_num)
  have h4 : (∑ d ∈ (3 ^ b * 35 : ℕ).divisors, (d : ℤ))
      = ((∑ d ∈ (3 ^ b * 35 : ℕ).divisors, d : ℕ) : ℤ) := by push_cast; ring
  rw [h4, h1, h2, h3]
  push_cast
  have h5 := two_mul_geom_sum (b + 1)
  linarith

/-- The inductive step gadget: from a set `T` of divisors of `35` and a set `A` of divisors of
`3 ^ b * 35` we build a set of divisors of `3 ^ (b + 1) * 35` whose sum is
`(∑ T) + 3 * (∑ A)`. -/
lemma step_aux {b : ℕ} {T A : Finset ℕ} (hT : ∀ x ∈ T, x ∣ 35)
    (hA : A ⊆ (3 ^ b * 35 : ℕ).divisors) :
    (T ∪ A.image (fun d => 3 * d)) ⊆ (3 ^ (b + 1) * 35 : ℕ).divisors ∧
      (∑ d ∈ (T ∪ A.image (fun d => 3 * d)), (d : ℤ))
        = (∑ d ∈ T, (d : ℤ)) + 3 * ∑ d ∈ A, (d : ℤ) := by
  have hpos : (3 ^ (b + 1) * 35 : ℕ) ≠ 0 := by positivity
  have hdisj : Disjoint T (A.image (fun d => 3 * d)) := by
    rw [Finset.disjoint_right]
    rintro x hx hxT
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have h35 : (3 * d) ∣ 35 := hT _ hxT
    have h3 : (3 : ℕ) ∣ 35 := dvd_trans ⟨d, rfl⟩ h35
    norm_num at h3
  constructor
  · intro x hx
    rw [Finset.mem_union] at hx
    rw [Nat.mem_divisors]
    refine ⟨?_, hpos⟩
    rcases hx with hx | hx
    · exact dvd_trans (hT _ hx) ⟨3 ^ (b + 1), by ring⟩
    · simp only [Finset.mem_image] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      obtain ⟨c, hc⟩ := (Nat.mem_divisors.mp (hA hd)).1
      refine ⟨c, ?_⟩
      calc 3 ^ (b + 1) * 35 = 3 * (3 ^ b * 35) := by ring
        _ = 3 * (d * c) := by rw [hc]
        _ = 3 * d * c := by ring
  · rw [Finset.sum_union hdisj,
      Finset.sum_image
        (by intro x _ y _ h; simpa using h : ∀ x ∈ A, ∀ y ∈ A, 3 * x = 3 * y → x = y)]
    push_cast
    rw [Finset.mul_sum]

/-- Key lemma: for `b ≥ 3`, every integer within `12` of half the sum of the divisors of
`3 ^ b * 35` is realised as the sum of a set of divisors of `3 ^ b * 35`. -/
lemma exists_subset_sum_shift : ∀ (b : ℕ), 3 ≤ b → ∀ δ : ℤ, -12 ≤ δ → δ ≤ 12 →
    ∃ A ⊆ (3 ^ b * 35 : ℕ).divisors, (∑ d ∈ A, (d : ℤ)) = 12 * (3 ^ (b + 1) - 1) + δ := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
      intro δ h1 h2
      have hkey : ∀ V : Finset ℕ, (∀ x ∈ V, x ∣ 945) →
          (∑ d ∈ V, (d : ℤ)) = 12 * (3 ^ (3 + 1) - 1) + δ →
          ∃ A ⊆ (3 ^ 3 * 35 : ℕ).divisors, (∑ d ∈ A, (d : ℤ)) = 12 * (3 ^ (3 + 1) - 1) + δ := by
        intro V hV hsum
        refine ⟨V, fun x hx => Nat.mem_divisors.mpr ⟨?_, by norm_num⟩, hsum⟩
        have h945 : ((3 : ℕ) ^ 3 * 35) = 945 := by norm_num
        rw [h945]
        exact hV x hx
      interval_cases δ
      · exact hkey {945, 3} (by decide) (by norm_num)
      · exact hkey {945, 1, 3} (by decide) (by norm_num)
      · exact hkey {945, 5} (by decide) (by norm_num)
      · exact hkey {945, 1, 5} (by decide) (by norm_num)
      · exact hkey {945, 7} (by decide) (by norm_num)
      · exact hkey {945, 1, 7} (by decide) (by norm_num)
      · exact hkey {945, 9} (by decide) (by norm_num)
      · exact hkey {945, 1, 9} (by decide) (by norm_num)
      · exact hkey {945, 1, 3, 7} (by decide) (by norm_num)
      · exact hkey {945, 3, 9} (by decide) (by norm_num)
      · exact hkey {945, 1, 3, 9} (by decide) (by norm_num)
      · exact hkey {945, 5, 9} (by decide) (by norm_num)
      · exact hkey {945, 15} (by decide) (by norm_num)
      · exact hkey {945, 1, 15} (by decide) (by norm_num)
      · exact hkey {945, 3, 5, 9} (by decide) (by norm_num)
      · exact hkey {945, 3, 15} (by decide) (by norm_num)
      · exact hkey {945, 1, 3, 15} (by decide) (by norm_num)
      · exact hkey {945, 5, 15} (by decide) (by norm_num)
      · exact hkey {945, 21} (by decide) (by norm_num)
      · exact hkey {945, 1, 21} (by decide) (by norm_num)
      · exact hkey {945, 1, 7, 15} (by decide) (by norm_num)
      · exact hkey {945, 3, 21} (by decide) (by norm_num)
      · exact hkey {945, 1, 3, 21} (by decide) (by norm_num)
      · exact hkey {945, 5, 21} (by decide) (by norm_num)
      · exact hkey {945, 27} (by decide) (by norm_num)
  | succ n hn ih =>
      intro δ h1 h2
      have main : ∀ (T : Finset ℕ) (δ' : ℤ), (∀ x ∈ T, x ∣ 35) → -12 ≤ δ' → δ' ≤ 12 →
          (∑ d ∈ T, (d : ℤ)) + 3 * δ' - 24 = δ →
          ∃ A ⊆ (3 ^ (n + 1) * 35 : ℕ).divisors,
            (∑ d ∈ A, (d : ℤ)) = 12 * (3 ^ (n + 1 + 1) - 1) + δ := by
        intro T δ' hT hd1 hd2 hrel
        obtain ⟨A, hA, hAsum⟩ := ih δ' hd1 hd2
        obtain ⟨hsub, hsum⟩ := step_aux hT hA
        refine ⟨_, hsub, ?_⟩
        rw [hsum, hAsum]
        have hp : (3 : ℤ) ^ (n + 1 + 1) = 3 * 3 ^ (n + 1) := by ring
        rw [hp]
        linarith
      rcases (by omega : δ % 3 = 0 ∨ δ % 3 = 1 ∨ δ % 3 = 2) with h | h | h
      · exact main {5, 7} ((δ + 12) / 3) (by decide) (by omega) (by omega) (by norm_num; omega)
      · exact main {1, 5, 7} ((δ + 11) / 3) (by decide) (by omega) (by omega) (by norm_num; omega)
      · exact main {1, 7} ((δ + 16) / 3) (by decide) (by omega) (by omega) (by norm_num; omega)

/-- For every `b ≥ 3`, the odd number `3 ^ b * 35` is a Zumkeller number. -/
theorem zumkeller_three_pow_mul_35 {b : ℕ} (hb : 3 ≤ b) : IsZumkeller (3 ^ b * 35) := by
  obtain ⟨A, hA, hAsum⟩ := exists_subset_sum_shift b hb 0 (by norm_num) (by norm_num)
  refine ⟨by positivity, A, hA, ?_⟩
  have hcast : ((2 * ∑ d ∈ A, d : ℕ) : ℤ) = ((∑ d ∈ (3 ^ b * 35 : ℕ).divisors, d : ℕ) : ℤ) := by
    push_cast
    rw [hAsum]
    have hσ := sum_divisors_three_pow_mul_35 b
    push_cast at hσ
    rw [hσ]
    ring
  exact_mod_cast hcast

/-- **Odd Zumkeller numbers from 3-structure.**

For every exponent `a ≥ 3` and every odd `m` coprime to `105 = 3 * 5 * 7`, the number
`n = 3 ^ a * 35 * m = 3 ^ a * 5 * 7 * m` is an odd Zumkeller number whose `3`-part is exactly
`3 ^ a`.  In particular the three-structure `3 ^ a * 5 * 7` with `a ≥ 3` generates odd
Zumkeller numbers. -/
theorem OddZumkellerFrom3Structure (a m : ℕ) (ha : 3 ≤ a) (hodd : Odd m)
    (hcop : Nat.Coprime 105 m) :
    Odd (3 ^ a * 35 * m) ∧ IsZumkeller (3 ^ a * 35 * m) ∧
      3 ^ a ∣ 3 ^ a * 35 * m ∧ ¬ (3 ^ (a + 1) ∣ 3 ^ a * 35 * m) := by
  have hm0 : 0 < m := by
    have := Nat.odd_iff.mp hodd
    omega
  have hc3 : Nat.Coprime 3 m := Nat.Coprime.coprime_dvd_left (by norm_num) hcop
  have hc35 : Nat.Coprime 35 m := Nat.Coprime.coprime_dvd_left (by norm_num) hcop
  have hcm : Nat.Coprime (3 ^ a * 35) m :=
    Nat.Coprime.mul_left (Nat.Coprime.pow_left _ hc3) hc35
  refine ⟨?_, zumkeller_mul_of_coprime (zumkeller_three_pow_mul_35 ha) hm0 hcm,
    ⟨35 * m, by ring⟩, ?_⟩
  · exact (Odd.mul (Odd.pow (by decide)) (by decide)).mul hodd
  · intro hdvd
    have h1 : (3 : ℕ) ^ a * 3 ∣ 3 ^ a * (35 * m) := by
      rw [← mul_assoc]
      rw [pow_succ] at hdvd
      exact hdvd
    have h2 : (3 : ℕ) ∣ 35 * m := (mul_dvd_mul_iff_left (by positivity : (3 : ℕ) ^ a ≠ 0)).mp h1
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h2 with h | h
    · norm_num at h
    · have h3 : (3 : ℕ) ∣ Nat.gcd 3 m := Nat.dvd_gcd dvd_rfl h
      rw [hc3] at h3
      norm_num at h3

/-- There are infinitely many odd Zumkeller numbers. -/
theorem infinite_odd_zumkeller : {n : ℕ | Odd n ∧ IsZumkeller n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨3 ^ 3 * 35 * 11 ^ N, ?_, ?_⟩
  · obtain ⟨h1, h2, -, -⟩ := OddZumkellerFrom3Structure 3 (11 ^ N) le_rfl
      (Odd.pow (by decide)) (Nat.Coprime.pow_right _ (by decide))
    exact ⟨h1, h2⟩
  · have hlt : N < 11 ^ N := Nat.lt_pow_self (by norm_num)
    nlinarith [pow_pos (show 0 < 11 by norm_num) N]

/-!
## Necessary conditions: the shape of an odd Zumkeller number

The family produced above uses the three smallest odd primes `3, 5, 7`.  This is optimal:
an odd Zumkeller number is never a prime power or a product of two prime powers.
-/

/-- A Zumkeller number is abundant or perfect: `σ(n) ≥ 2 * n`. -/
theorem zumkeller_two_mul_le_sigma {n : ℕ} (h : IsZumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hpos, A, hA, hsum⟩ := h
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hpos.ne'
  have key : n ≤ ∑ d ∈ A, d := by
    by_cases hn : n ∈ A
    · exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hn
    · have hmem' : n ∈ n.divisors \ A := Finset.mem_sdiff.mpr ⟨hmem, hn⟩
      have h1 : n ≤ ∑ d ∈ n.divisors \ A, d :=
        Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hmem'
      have h2 : ∑ d ∈ n.divisors \ A, d + ∑ d ∈ A, d = ∑ d ∈ n.divisors, d :=
        Finset.sum_sdiff hA
      omega
  omega

/-- A geometric-sum identity, stated without natural subtraction. -/
lemma pow_mul_geom (p a : ℕ) :
    p * (∑ i ∈ Finset.range (a + 1), p ^ i) + 1
      = (∑ i ∈ Finset.range (a + 1), p ^ i) + p ^ (a + 1) := by
  induction a with
  | zero => simp; omega
  | succ k ih =>
      rw [Finset.sum_range_succ]
      ring_nf
      ring_nf at ih
      nlinarith [ih, pow_succ p (k + 1)]

/-- For a prime `p ≥ 3`, `σ(p ^ a) < (3 / 2) * p ^ a`. -/
lemma two_sigma_lt_three {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (a : ℕ) :
    2 * ∑ d ∈ (p ^ a).divisors, d < 3 * p ^ a := by
  have hS : ∑ d ∈ (p ^ a : ℕ).divisors, d = ∑ i ∈ Finset.range (a + 1), p ^ i :=
    Nat.sum_divisors_prime_pow hp
  rw [hS]
  set S := ∑ i ∈ Finset.range (a + 1), p ^ i with hSdef
  have hid := pow_mul_geom p a
  have hpos : 0 < p ^ a := pow_pos (by omega) a
  have hSpos : 0 < S := by
    rw [hSdef]
    exact Finset.sum_pos (fun i _ => pow_pos (by omega) i) ⟨0, by simp⟩
  have hpow : p ^ (a + 1) = p * p ^ a := by ring
  nlinarith [hid, hpow]

/-- For a prime `q ≥ 5`, `σ(q ^ b) < (5 / 4) * q ^ b`. -/
lemma four_sigma_lt_five {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (b : ℕ) :
    4 * ∑ d ∈ (q ^ b).divisors, d < 5 * q ^ b := by
  have hS : ∑ d ∈ (q ^ b : ℕ).divisors, d = ∑ i ∈ Finset.range (b + 1), q ^ i :=
    Nat.sum_divisors_prime_pow hq
  rw [hS]
  set S := ∑ i ∈ Finset.range (b + 1), q ^ i with hSdef
  have hid := pow_mul_geom q b
  have hpos : 0 < q ^ b := pow_pos (by omega) b
  have hSpos : 0 < S := by
    rw [hSdef]
    exact Finset.sum_pos (fun i _ => pow_pos (by omega) i) ⟨0, by simp⟩
  have hpow : q ^ (b + 1) = q * q ^ b := by ring
  nlinarith [hid, hpow]

/-- A product of two odd prime powers with distinct primes is deficient. -/
lemma sigma_lt_two_mul_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h3 : 3 ≤ p) (h5 : 5 ≤ q) (hne : p ≠ q) (e f : ℕ) :
    ∑ d ∈ (p ^ e * q ^ f).divisors, d < 2 * (p ^ e * q ^ f) := by
  have hcop : Nat.Coprime (p ^ e) (q ^ f) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hne)
  rw [Nat.Coprime.sum_divisors_mul hcop]
  have h1 := two_sigma_lt_three hp h3 e
  have h2 := four_sigma_lt_five hq h5 f
  have hep : 0 < p ^ e := pow_pos (by omega) e
  have hfq : 0 < q ^ f := pow_pos (by omega) f
  have hprod : (2 * ∑ d ∈ (p ^ e).divisors, d) * (4 * ∑ d ∈ (q ^ f).divisors, d)
      < (3 * p ^ e) * (5 * q ^ f) := Nat.mul_lt_mul_of_lt_of_lt h1 h2
  by_contra hcon
  push_neg at hcon
  have hPQ : 0 < p ^ e * q ^ f := Nat.mul_pos hep hfq
  nlinarith [hprod, hcon, hPQ]

/-- A prime `≥ 3` which is not `3` is `≥ 5`. -/
lemma five_le_of_prime {q : ℕ} (hq : q.Prime) (h3 : 3 ≤ q) (hne : q ≠ 3) : 5 ≤ q := by
  by_contra hlt
  push_neg at hlt
  interval_cases q
  · exact hne rfl
  · exact absurd hq (by decide)

/-- **Every odd Zumkeller number has at least three distinct prime factors.**
Hence the structure `3 ^ a * 5 * 7 * m` used above realises the smallest possible set of
prime factors. -/
theorem odd_zumkeller_three_primeFactors {n : ℕ} (hodd : Odd n) (hz : IsZumkeller n) :
    3 ≤ n.primeFactors.card := by
  by_contra hc
  push_neg at hc
  have hpos := hz.1
  have hn0 : n ≠ 0 := hpos.ne'
  have habund := zumkeller_two_mul_le_sigma hz
  have hoddp : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have h2 := hpp.two_le
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · exfalso
      interval_cases p
      · rw [Nat.odd_iff] at hodd
        obtain ⟨c, rfl⟩ := hdvd
        omega
    · exact hge
  have hsigma : ∑ d ∈ n.divisors, d < 2 * n := by
    have hcases : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 := by
      omega
    rcases hcases with h0 | h1 | h2
    · have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp h0
      have hn1 : n = 1 := by
        rcases Nat.primeFactors_eq_empty.mp hempty with h | h
        · exact absurd h hn0
        · exact h
      subst hn1
      simp
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
      have hmp : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmp
      have hp3 : 3 ≤ p := hoddp p hmp
      have hfac : n = p ^ (n.factorization p) := by
        have h1' := Nat.factorization_prod_pow_eq_self hn0
        rw [Finsupp.prod, Nat.support_factorization, hp, Finset.prod_singleton] at h1'
        exact h1'.symm
      rw [hfac]
      have hlt := two_sigma_lt_three hpp hp3 (n.factorization p)
      have hpe : 0 < p ^ (n.factorization p) := pow_pos (by omega) _
      omega
    · obtain ⟨p, q, hne, hpq⟩ := Finset.card_eq_two.mp h2
      have hmp : p ∈ n.primeFactors := by rw [hpq]; simp
      have hmq : q ∈ n.primeFactors := by rw [hpq]; simp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hmp
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hmq
      have hp3 : 3 ≤ p := hoddp p hmp
      have hq3 : 3 ≤ q := hoddp q hmq
      have hfac : n = p ^ (n.factorization p) * q ^ (n.factorization q) := by
        have h1' := Nat.factorization_prod_pow_eq_self hn0
        rw [Finsupp.prod, Nat.support_factorization, hpq, Finset.prod_pair hne] at h1'
        exact h1'.symm
      by_cases hp_eq3 : p = 3
      · have hq5 : 5 ≤ q := five_le_of_prime hqp hq3 (by omega)
        rw [hfac]
        exact sigma_lt_two_mul_two_primes hpp hqp hp3 hq5 hne _ _
      · have hp5 : 5 ≤ p := five_le_of_prime hpp hp3 hp_eq3
        rw [hfac, mul_comm]
        exact sigma_lt_two_mul_two_primes hqp hpp hq3 hp5 (Ne.symm hne) _ _
  omega

end Brockian.ZumkellerNumbers

