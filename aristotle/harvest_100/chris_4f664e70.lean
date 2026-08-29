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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *unitary divisor* of `n` is a divisor `d` with `gcd d (n / d) = 1`, and `n` is *unitary
perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.  Exactly five unitary
perfect numbers are known:

`6`, `60`, `90`, `87360`, `146361946186458562560000`,

and whether a sixth one exists is an open problem.  This file develops the basic theory
(`σ*` is multiplicative, `σ*(p^a) = 1 + p^a`, the factorization formula), verifies the five
known examples, proves that every unitary perfect number is even, and reduces the existence
of a sixth unitary perfect number to an explicit arithmetic criterion on the odd part.
-/

open Finset

namespace Brockian.UnitaryPerfect

/-- The unitary divisors of `n`: divisors `d` of `n` with `gcd d (n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => Nat.Coprime d (n / d)

/-- `usigma n = σ*(n)` is the sum of the unitary divisors of `n`. -/
def usigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is unitary perfect if it is positive and the sum of its unitary divisors is `2 * n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ usigma n = 2 * n

/-- The five known unitary perfect numbers. -/
def knownUnitaryPerfect : Finset ℕ := {6, 60, 90, 87360, 146361946186458562560000}

theorem mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

theorem usigma_zero : usigma 0 = 0 := by simp [usigma, unitaryDivisors]

theorem usigma_one : usigma 1 = 1 := by decide

/-! ### Multiplicativity of `σ*` -/

/-- `σ*` is multiplicative: the map `(a, b) ↦ a * b` is a bijection from pairs of unitary
divisors of coprime `m`, `n` onto the unitary divisors of `m * n`. -/
theorem usigma_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  unfold usigma
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine (Finset.sum_nbij' (i := fun x => x.1 * x.2) (j := fun d => (Nat.gcd d m, Nat.gcd d n))
    ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product] at hab
    obtain ⟨ha, hb⟩ := hab
    rw [mem_unitaryDivisors] at ha hb ⊢
    obtain ⟨ha1, -, ha2⟩ := ha
    obtain ⟨hb1, -, hb2⟩ := hb
    have hdiv : m * n / (a * b) = (m / a) * (n / b) := Nat.mul_div_mul_comm ha1 hb1
    refine ⟨mul_dvd_mul ha1 hb1, by positivity, ?_⟩
    rw [hdiv]
    have ham : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left ha1 h
    have hbn : Nat.Coprime b m := Nat.Coprime.coprime_dvd_left hb1 h.symm
    exact Nat.Coprime.mul_left
      (Nat.Coprime.mul_right ha2 (ham.coprime_dvd_right (Nat.div_dvd_of_dvd hb1)))
      (Nat.Coprime.mul_right (hbn.coprime_dvd_right (Nat.div_dvd_of_dvd ha1)) hb2)
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hd1, -, hd2⟩ := hd
    have hgm : Nat.gcd d m ∣ m := Nat.gcd_dvd_right d m
    have hgn : Nat.gcd d n ∣ n := Nat.gcd_dvd_right d n
    have hsplit : Nat.gcd d m * Nat.gcd d n = d := by
      rw [← h.gcd_mul d, Nat.gcd_eq_left hd1]
    have hdiv : m * n / d = (m / Nat.gcd d m) * (n / Nat.gcd d n) := by
      calc m * n / d = m * n / (Nat.gcd d m * Nat.gcd d n) := by rw [hsplit]
        _ = (m / Nat.gcd d m) * (n / Nat.gcd d n) := Nat.mul_div_mul_comm hgm hgn
    rw [hdiv] at hd2
    simp only [Finset.mem_product, mem_unitaryDivisors]
    exact ⟨⟨hgm, hm, (hd2.coprime_dvd_left (Nat.gcd_dvd_left d m)).coprime_dvd_right
        (Dvd.intro _ rfl)⟩,
      ⟨hgn, hn, (hd2.coprime_dvd_left (Nat.gcd_dvd_left d n)).coprime_dvd_right
        (Dvd.intro_left _ rfl)⟩⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ha1, -, -⟩, ⟨hb1, -, -⟩⟩ := hab
    have ham : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left ha1 h
    have hbn : Nat.Coprime b m := Nat.Coprime.coprime_dvd_left hb1 h.symm
    have h1 : Nat.gcd (a * b) m = a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a hbn, Nat.gcd_eq_left ha1]
    have h2 : Nat.gcd (a * b) n = b := by
      rw [Nat.Coprime.gcd_mul_left_cancel b ham, Nat.gcd_eq_left hb1]
    simp [h1, h2]
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    show Nat.gcd d m * Nat.gcd d n = d
    rw [← h.gcd_mul d, Nat.gcd_eq_left hd.1]
  · rintro ⟨a, b⟩ _; rfl

/-- Multiplicativity of `σ*` without positivity assumptions. -/
theorem usigma_mul_of_coprime' (m n : ℕ) (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at h
    subst h; simp [usigma_zero, usigma_one]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at h
    subst h; simp [usigma_zero, usigma_one]
  exact usigma_mul_of_coprime hm hn h

/-- A prime power has exactly two unitary divisors, `1` and itself. -/
theorem unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  have hppos : 0 < p := hp.pos
  ext d
  simp only [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, -, hcop⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
    rw [Nat.pow_div hi hppos] at hcop
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · left; simp
    · right
      have hki : k - i = 0 := by
        by_contra hne
        have hpd : p ∣ Nat.gcd (p ^ i) (p ^ (k - i)) :=
          Nat.dvd_gcd (dvd_pow_self p hipos.ne') (dvd_pow_self p hne)
        rw [hcop] at hpd
        exact hp.one_lt.ne' (Nat.dvd_one.mp hpd)
      have hik : i = k := by omega
      rw [hik]
  · rintro (rfl | rfl)
    · exact ⟨one_dvd _, pow_ne_zero _ hppos.ne', by simp⟩
    · refine ⟨dvd_rfl, pow_ne_zero _ hppos.ne', ?_⟩
      simp [Nat.div_self (pow_pos hppos k)]

theorem usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : usigma (p ^ k) = 1 + p ^ k := by
  have h1 : (1 : ℕ) < p ^ k :=
    calc 1 < p := hp.one_lt
      _ ≤ p ^ k := Nat.le_self_pow hk p
  rw [usigma, unitaryDivisors_prime_pow hp, Finset.sum_pair h1.ne]

theorem usigma_prime {p : ℕ} (hp : p.Prime) : usigma p = 1 + p := by
  simpa using usigma_prime_pow (k := 1) hp one_ne_zero

/-- Multiplicativity, in the convenient "peel off a prime power" form. -/
theorem usigma_prime_pow_mul {p k r : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hr : r ≠ 0)
    (h : Nat.Coprime (p ^ k) r) : usigma (p ^ k * r) = (1 + p ^ k) * usigma r := by
  rw [usigma_mul_of_coprime (pow_ne_zero _ hp.pos.ne') hr h, usigma_prime_pow hp hk]

theorem usigma_prime_mul {p r : ℕ} (hp : p.Prime) (hr : r ≠ 0) (h : Nat.Coprime p r) :
    usigma (p * r) = (1 + p) * usigma r := by
  rw [usigma_mul_of_coprime hp.pos.ne' hr h, usigma_prime hp]

/-- The factorization formula `σ*(n) = ∏_{p^a ‖ n} (1 + p^a)`. -/
theorem usigma_eq_prod_primeFactors {n : ℕ} (hn : n ≠ 0) :
    usigma n = ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [Nat.multiplicative_factorization usigma usigma_mul_of_coprime' usigma_one hn,
    Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hk : n.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
  exact usigma_prime_pow (Nat.prime_of_mem_primeFactors hp) hk

theorem prod_pow_factorization_self {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-! ### The five known unitary perfect numbers -/

theorem usigma_six : usigma 6 = 12 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num,
    usigma_prime_mul (p := 2) (by norm_num) (by norm_num) (by norm_num),
    usigma_prime (p := 3) (by norm_num)]

theorem usigma_sixty : usigma 60 = 120 := by
  have h5 : usigma 15 = 24 := by
    rw [show (15 : ℕ) = 3 * 5 by norm_num,
      usigma_prime_mul (p := 3) (by norm_num) (by norm_num) (by norm_num),
      usigma_prime (p := 5) (by norm_num)]
  rw [show (60 : ℕ) = 2 ^ 2 * 15 by norm_num,
    usigma_prime_pow_mul (p := 2) (k := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), h5]
  norm_num

theorem usigma_ninety : usigma 90 = 180 := by
  have h5 : usigma 5 = 6 := by rw [usigma_prime (p := 5) (by norm_num)]
  have h9 : usigma 45 = 60 := by
    rw [show (45 : ℕ) = 3 ^ 2 * 5 by norm_num,
      usigma_prime_pow_mul (p := 3) (k := 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), h5]
    norm_num
  rw [show (90 : ℕ) = 2 * 45 by norm_num,
    usigma_prime_mul (p := 2) (by norm_num) (by norm_num) (by norm_num), h9]

theorem usigma_87360 : usigma 87360 = 174720 := by
  have h13 : usigma 13 = 14 := by rw [usigma_prime (p := 13) (by norm_num)]
  have h7 : usigma 91 = 112 := by
    rw [show (91 : ℕ) = 7 * 13 by norm_num,
      usigma_prime_mul (p := 7) (by norm_num) (by norm_num) (by norm_num), h13]
  have h5 : usigma 455 = 672 := by
    rw [show (455 : ℕ) = 5 * 91 by norm_num,
      usigma_prime_mul (p := 5) (by norm_num) (by norm_num) (by norm_num), h7]
  have h3 : usigma 1365 = 2688 := by
    rw [show (1365 : ℕ) = 3 * 455 by norm_num,
      usigma_prime_mul (p := 3) (by norm_num) (by norm_num) (by norm_num), h5]
  rw [show (87360 : ℕ) = 2 ^ 6 * 1365 by norm_num,
    usigma_prime_pow_mul (p := 2) (k := 6) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), h3]
  norm_num

theorem usigma_big : usigma 146361946186458562560000 = 292723892372917125120000 := by
  have h11 : usigma 313 = 314 := by rw [usigma_prime (p := 313) (by norm_num)]
  have h10 : usigma 49141 = 49612 := by
    rw [show (49141 : ℕ) = 157 * 313 by norm_num,
      usigma_prime_mul (p := 157) (by norm_num) (by norm_num) (by norm_num), h11]
  have h9 : usigma 5356369 = 5457320 := by
    rw [show (5356369 : ℕ) = 109 * 49141 by norm_num,
      usigma_prime_mul (p := 109) (by norm_num) (by norm_num) (by norm_num), h10]
  have h8 : usigma 423153151 = 436585600 := by
    rw [show (423153151 : ℕ) = 79 * 5356369 by norm_num,
      usigma_prime_mul (p := 79) (by norm_num) (by norm_num) (by norm_num), h9]
  have h7 : usigma 15656666587 = 16590252800 := by
    rw [show (15656666587 : ℕ) = 37 * 423153151 by norm_num,
      usigma_prime_mul (p := 37) (by norm_num) (by norm_num) (by norm_num), h8]
  have h6 : usigma 297476665153 = 331805056000 := by
    rw [show (297476665153 : ℕ) = 19 * 15656666587 by norm_num,
      usigma_prime_mul (p := 19) (by norm_num) (by norm_num) (by norm_num), h7]
  have h5 : usigma 3867196646989 = 4645270784000 := by
    rw [show (3867196646989 : ℕ) = 13 * 297476665153 by norm_num,
      usigma_prime_mul (p := 13) (by norm_num) (by norm_num) (by norm_num), h6]
  have h4 : usigma 42539163116879 = 55743249408000 := by
    rw [show (42539163116879 : ℕ) = 11 * 3867196646989 by norm_num,
      usigma_prime_mul (p := 11) (by norm_num) (by norm_num) (by norm_num), h5]
  have h3 : usigma 297774141818153 = 445945995264000 := by
    rw [show (297774141818153 : ℕ) = 7 * 42539163116879 by norm_num,
      usigma_prime_mul (p := 7) (by norm_num) (by norm_num) (by norm_num), h4]
  have h2 : usigma 186108838636345625 = 279162193035264000 := by
    rw [show (186108838636345625 : ℕ) = 5 ^ 4 * 297774141818153 by norm_num,
      usigma_prime_pow_mul (p := 5) (k := 4) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), h3]
    norm_num
  have h1 : usigma 558326515909036875 = 1116648772141056000 := by
    rw [show (558326515909036875 : ℕ) = 3 * 186108838636345625 by norm_num,
      usigma_prime_mul (p := 3) (by norm_num) (by norm_num) (by norm_num), h2]
  rw [show (146361946186458562560000 : ℕ) = 2 ^ 18 * 558326515909036875 by norm_num,
    usigma_prime_pow_mul (p := 2) (k := 18) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), h1]
  norm_num

theorem isUnitaryPerfect_six : IsUnitaryPerfect 6 := ⟨by norm_num, by rw [usigma_six]⟩

theorem isUnitaryPerfect_sixty : IsUnitaryPerfect 60 := ⟨by norm_num, by rw [usigma_sixty]⟩

theorem isUnitaryPerfect_ninety : IsUnitaryPerfect 90 := ⟨by norm_num, by rw [usigma_ninety]⟩

theorem isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := ⟨by norm_num, by rw [usigma_87360]⟩

theorem isUnitaryPerfect_big : IsUnitaryPerfect 146361946186458562560000 :=
  ⟨by norm_num, by rw [usigma_big]⟩

/-- All five members of `knownUnitaryPerfect` really are unitary perfect. -/
theorem isUnitaryPerfect_of_mem_known {n : ℕ} (hn : n ∈ knownUnitaryPerfect) :
    IsUnitaryPerfect n := by
  simp only [knownUnitaryPerfect, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact isUnitaryPerfect_six
  · exact isUnitaryPerfect_sixty
  · exact isUnitaryPerfect_ninety
  · exact isUnitaryPerfect_87360
  · exact isUnitaryPerfect_big

/-! ### Every unitary perfect number is even -/

/-- There is no odd unitary perfect number: if `n` is odd with `k` distinct prime factors,
then `2 ^ k ∣ σ*(n)`, which forces `k ≤ 1`, and both remaining cases are impossible. -/
theorem not_isUnitaryPerfect_of_odd {n : ℕ} (hodd : Odd n) : ¬ IsUnitaryPerfect n := by
  rintro ⟨hpos, heq⟩
  have hn : n ≠ 0 := hpos.ne'
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  have h2 : ¬ (2 ∣ n) := by omega
  have hprod := usigma_eq_prod_primeFactors hn
  have hdvd : 2 ^ n.primeFactors.card ∣ usigma n := by
    rw [hprod, ← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpodd : Odd p := by
      rcases Nat.even_or_odd p with he | ho
      · exact absurd (dvd_trans he.two_dvd hpdvd) h2
      · exact ho
    exact (Odd.add_odd odd_one hpodd.pow).two_dvd
  rcases lt_trichotomy n.primeFactors.card 1 with hc | hc | hc
  · have hcard : n.primeFactors.card = 0 := by omega
    have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard
    have hn1 : n = 1 := by
      rcases Nat.primeFactors_eq_empty.mp hempty with h | h
      · exact absurd h hn
      · exact h
    rw [hn1, usigma_one] at heq
    omega
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hprod2 : usigma n = 1 + n := by
      rw [hprod, hp, Finset.prod_singleton]
      have hpow : ∏ q ∈ n.primeFactors, q ^ n.factorization q = n :=
        prod_pow_factorization_self hn
      rw [hp, Finset.prod_singleton] at hpow
      rw [hpow]
    rw [hprod2] at heq
    have hn1 : n = 1 := by omega
    have hempty : n.primeFactors = ∅ := by rw [hn1]; simp
    rw [hempty] at hp
    simp at hp
  · have h4 : (4 : ℕ) ∣ usigma n :=
      dvd_trans (by norm_num) (dvd_trans (pow_dvd_pow 2 hc) hdvd)
    rw [heq] at h4
    omega

/-- Every unitary perfect number is even. -/
theorem even_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exact absurd h (not_isUnitaryPerfect_of_odd ho)

/-! ### Reduction to the odd part -/

/-- Reduction of unitary perfection of an even number to a relation on its odd part. -/
theorem isUnitaryPerfect_iff_odd_part {a m : ℕ} (ha : 1 ≤ a) (hm : Odd m) :
    IsUnitaryPerfect (2 ^ a * m) ↔ (1 + 2 ^ a) * usigma m = 2 ^ (a + 1) * m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hpos : 0 < 2 ^ a * m := by positivity
  rw [IsUnitaryPerfect, usigma_prime_pow_mul Nat.prime_two (by omega) hm0 hcop]
  constructor
  · rintro ⟨-, h⟩
    rw [h, pow_succ]; ring
  · intro h
    exact ⟨hpos, by rw [h, pow_succ]; ring⟩

/-- **Conditional statement.**  Whether a sixth unitary perfect number exists is an open
problem: only five unitary perfect numbers are known, and no proof of existence (or of
nonexistence) of a further one is known.  What is proved here is the reduction of the
question to a concrete arithmetic search: since every unitary perfect number is even (see
`not_isUnitaryPerfect_of_odd`), the existence of a sixth unitary perfect number follows from
-- and, by `sixthUnitaryPerfect_criterion`, is equivalent to -- the existence of an exponent
`a ≥ 1` and an odd number `m` satisfying `(1 + 2 ^ a) * σ*(m) = 2 ^ (a + 1) * m` with
`2 ^ a * m` not one of the five known unitary perfect numbers. -/
theorem SixthUnitaryPerfectExists
    (h : ∃ a m : ℕ, 1 ≤ a ∧ Odd m ∧ (1 + 2 ^ a) * usigma m = 2 ^ (a + 1) * m ∧
      2 ^ a * m ∉ knownUnitaryPerfect) :
    ∃ n : ℕ, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect := by
  obtain ⟨a, m, ha, hm, heq, hnot⟩ := h
  exact ⟨2 ^ a * m, (isUnitaryPerfect_iff_odd_part ha hm).2 heq, hnot⟩

/-- The criterion used in `SixthUnitaryPerfectExists` is not just sufficient but necessary:
a sixth unitary perfect number exists if and only if the displayed equation has a solution
outside the five known numbers. -/
theorem sixthUnitaryPerfect_criterion :
    (∃ n : ℕ, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect) ↔
      (∃ a m : ℕ, 1 ≤ a ∧ Odd m ∧ (1 + 2 ^ a) * usigma m = 2 ^ (a + 1) * m ∧
        2 ^ a * m ∉ knownUnitaryPerfect) := by
  constructor
  · rintro ⟨n, hup, hnot⟩
    have hn : n ≠ 0 := hup.1.ne'
    have heven : 2 ∣ n := (even_of_isUnitaryPerfect hup).two_dvd
    have ha : 1 ≤ n.factorization 2 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn heven
    have hsplit : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n 2
    have hmodd : Odd (n / 2 ^ n.factorization 2) := by
      have h := Nat.not_dvd_ordCompl Nat.prime_two hn
      rw [Nat.odd_iff]
      omega
    exact ⟨n.factorization 2, n / 2 ^ n.factorization 2, ha, hmodd,
      (isUnitaryPerfect_iff_odd_part ha hmodd).1 (by rwa [hsplit]), by rwa [hsplit]⟩
  · rintro ⟨a, m, ha, hm, heq, hnot⟩
    exact ⟨2 ^ a * m, (isUnitaryPerfect_iff_odd_part ha hm).2 heq, hnot⟩

end Brockian.UnitaryPerfect

