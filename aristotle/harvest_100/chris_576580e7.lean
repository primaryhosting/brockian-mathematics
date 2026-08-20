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

A *unitary divisor* of `n` is a divisor `d` with `gcd (d, n / d) = 1`, and `n` is *unitary
perfect* if the sum `σ*(n)` of its unitary divisors equals `2 n`.  Exactly five unitary
perfect numbers are known:

`6, 60, 90, 87360, 146361946186458562560000`,

and it is a long-standing open problem whether a sixth one exists.  Accordingly this file
does **not** prove unconditional existence; it develops the basic theory of `σ*`
(multiplicativity, values at prime powers), verifies that the five known numbers really are
unitary perfect, proves that every unitary perfect number is even, and finally proves the
target statement `SixthUnitaryPerfectExists` as a *conditional reduction*: any unitary
perfect number that either exceeds the largest known one or fails to be divisible by `3`
is a sixth unitary perfect number.

(The header comment above appears after the `import` line only because Lean requires
imports to come first in a file.)
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => Nat.Coprime d (n / d)

/-- The sum-of-unitary-divisors function `σ*`. -/
def usigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is unitary perfect if it is positive and `σ*(n) = 2 n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ usigma n = 2 * n

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

lemma usigma_zero : usigma 0 = 0 := by simp [usigma, unitaryDivisors]

lemma usigma_one : usigma 1 = 1 := by decide

/-- `σ*` is multiplicative. -/
lemma usigma_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [Nat.coprime_zero_left] at h
    subst h; simp [usigma_zero, usigma_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.coprime_zero_right] at h
    subst h; simp [usigma_zero, usigma_one]
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun d => (d.gcd m, d.gcd n)) (fun x => x.1 * x.2) ?_ ?_ ?_ ?_ ?_
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hdvd, -, hcop⟩ := hd
    have key : d.gcd m * d.gcd n = d := by
      rw [← h.gcd_mul d, Nat.gcd_eq_left hdvd]
    have hmn : (m * n) / d = (m / d.gcd m) * (n / d.gcd n) := by
      rw [Nat.div_mul_div_comm (Nat.gcd_dvd_right d m) (Nat.gcd_dvd_right d n), key]
    rw [hmn] at hcop
    simp only [Finset.mem_product, mem_unitaryDivisors]
    exact ⟨⟨Nat.gcd_dvd_right d m, hm,
        Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d m)
          (hcop.coprime_dvd_right (dvd_mul_right _ _))⟩,
      ⟨Nat.gcd_dvd_right d n, hn,
        Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d n)
          (hcop.coprime_dvd_right (dvd_mul_left _ _))⟩⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ha, -, hca⟩, ⟨hb, -, hcb⟩⟩ := hab
    have hdiv : (m * n) / (a * b) = (m / a) * (n / b) :=
      (Nat.div_mul_div_comm ha hb).symm
    rw [mem_unitaryDivisors, hdiv]
    refine ⟨mul_dvd_mul ha hb, Nat.mul_ne_zero hm hn, ?_⟩
    have hamn : Nat.Coprime a (n / b) :=
      (h.coprime_dvd_left ha).coprime_dvd_right (Nat.div_dvd_of_dvd hb)
    have hbmn : Nat.Coprime b (m / a) :=
      (h.symm.coprime_dvd_left hb).coprime_dvd_right (Nat.div_dvd_of_dvd ha)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hca hamn)
      (Nat.Coprime.mul_right hbmn hcb)
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    show d.gcd m * d.gcd n = d
    rw [← h.gcd_mul d, Nat.gcd_eq_left hd.1]
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ha, -, hca⟩, ⟨hb, -, hcb⟩⟩ := hab
    have hbm : Nat.Coprime b m := h.symm.coprime_dvd_left hb
    have han : Nat.Coprime a n := h.coprime_dvd_left ha
    have h1 : (a * b).gcd m = a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a hbm, Nat.gcd_eq_left ha]
    have h2 : (a * b).gcd n = b := by
      rw [mul_comm, Nat.Coprime.gcd_mul_right_cancel b han, Nat.gcd_eq_left hb]
    simp [h1, h2]
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    show d = d.gcd m * d.gcd n
    rw [← h.gcd_mul d, Nat.gcd_eq_left hd.1]

/-- The unitary divisors of a prime power `p ^ k` (`k ≥ 1`) are `1` and `p ^ k`. -/
lemma usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    usigma (p ^ k) = 1 + p ^ k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hne : (1 : ℕ) ≠ p ^ k := (Nat.one_lt_pow hk hp.one_lt).ne
  have hset : unitaryDivisors (p ^ k) = {1, p ^ k} := by
    ext d
    simp only [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, -, hcop⟩
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · left; simp
      · right
        have hdiv : p ^ k / p ^ i = p ^ (k - i) := by
          rw [← pow_sub_mul_pow p hi, Nat.mul_div_cancel _ (pow_pos hp.pos i)]
        rw [hdiv] at hcop
        have hki : k - i = 0 := by
          by_contra hne'
          have h1 : p ∣ p ^ i := dvd_pow_self p hipos.ne'
          have h2 : p ∣ p ^ (k - i) := dvd_pow_self p hne'
          exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
        congr 1
        omega
    · rintro (rfl | rfl)
      · exact ⟨one_dvd _, hpk, by simp⟩
      · exact ⟨dvd_rfl, hpk, by simp [Nat.div_self (Nat.pos_of_ne_zero hpk)]⟩
  rw [usigma, hset, Finset.sum_pair hne]

lemma usigma_mul_prime_pow {m p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (h : ¬ p ∣ m) : usigma (m * p ^ k) = usigma m * (1 + p ^ k) := by
  have hcop : Nat.Coprime m (p ^ k) :=
    (((Nat.Prime.coprime_iff_not_dvd hp).mpr h).symm).pow_right k
  rw [usigma_mul_of_coprime hcop, usigma_prime_pow hp hk]

/-! ## The five known unitary perfect numbers -/

/-- The five known unitary perfect numbers. -/
def knownUnitaryPerfect : Finset ℕ := {6, 60, 90, 87360, 146361946186458562560000}

lemma isUnitaryPerfect_six : IsUnitaryPerfect 6 := by
  refine ⟨by norm_num, ?_⟩
  have h0 : usigma 2 = 3 := by
    have e : (2 : ℕ) = 2 ^ 1 := by norm_num
    rw [e, usigma_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have h1 : usigma 6 = 12 := by
    have e : (6 : ℕ) = 2 * 3 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h0]
    norm_num
  rw [h1]

lemma isUnitaryPerfect_sixty : IsUnitaryPerfect 60 := by
  refine ⟨by norm_num, ?_⟩
  have h0 : usigma 4 = 5 := by
    have e : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [e, usigma_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have h1 : usigma 12 = 20 := by
    have e : (12 : ℕ) = 4 * 3 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h0]
    norm_num
  have h2 : usigma 60 = 120 := by
    have e : (60 : ℕ) = 12 * 5 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h1]
    norm_num
  rw [h2]

lemma isUnitaryPerfect_ninety : IsUnitaryPerfect 90 := by
  refine ⟨by norm_num, ?_⟩
  have h0 : usigma 2 = 3 := by
    have e : (2 : ℕ) = 2 ^ 1 := by norm_num
    rw [e, usigma_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have h1 : usigma 18 = 30 := by
    have e : (18 : ℕ) = 2 * 3 ^ 2 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h0]
    norm_num
  have h2 : usigma 90 = 180 := by
    have e : (90 : ℕ) = 18 * 5 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h1]
    norm_num
  rw [h2]

lemma isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  refine ⟨by norm_num, ?_⟩
  have h0 : usigma 64 = 65 := by
    have e : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [e, usigma_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have h1 : usigma 192 = 260 := by
    have e : (192 : ℕ) = 64 * 3 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h0]
    norm_num
  have h2 : usigma 960 = 1560 := by
    have e : (960 : ℕ) = 192 * 5 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h1]
    norm_num
  have h3 : usigma 6720 = 12480 := by
    have e : (6720 : ℕ) = 960 * 7 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h2]
    norm_num
  have h4 : usigma 87360 = 174720 := by
    have e : (87360 : ℕ) = 6720 * 13 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h3]
    norm_num
  rw [h4]

lemma isUnitaryPerfect_N5 : IsUnitaryPerfect 146361946186458562560000 := by
  refine ⟨by norm_num, ?_⟩
  have h0 : usigma 262144 = 262145 := by
    have e : (262144 : ℕ) = 2 ^ 18 := by norm_num
    rw [e, usigma_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have h1 : usigma 786432 = 1048580 := by
    have e : (786432 : ℕ) = 262144 * 3 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h0]
    norm_num
  have h2 : usigma 491520000 = 656411080 := by
    have e : (491520000 : ℕ) = 786432 * 5 ^ 4 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h1]
    norm_num
  have h3 : usigma 3440640000 = 5251288640 := by
    have e : (3440640000 : ℕ) = 491520000 * 7 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h2]
    norm_num
  have h4 : usigma 37847040000 = 63015463680 := by
    have e : (37847040000 : ℕ) = 3440640000 * 11 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h3]
    norm_num
  have h5 : usigma 492011520000 = 882216491520 := by
    have e : (492011520000 : ℕ) = 37847040000 * 13 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h4]
    norm_num
  have h6 : usigma 9348218880000 = 17644329830400 := by
    have e : (9348218880000 : ℕ) = 492011520000 * 19 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h5]
    norm_num
  have h7 : usigma 345884098560000 = 670484533555200 := by
    have e : (345884098560000 : ℕ) = 9348218880000 * 37 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h6]
    norm_num
  have h8 : usigma 27324843786240000 = 53638762684416000 := by
    have e : (27324843786240000 : ℕ) = 345884098560000 * 79 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h7]
    norm_num
  have h9 : usigma 2978407972700160000 = 5900263895285760000 := by
    have e : (2978407972700160000 : ℕ) = 27324843786240000 * 109 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h8]
    norm_num
  have h10 : usigma 467610051713925120000 = 932241695455150080000 := by
    have e : (467610051713925120000 : ℕ) = 2978407972700160000 * 157 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h9]
    norm_num
  have h11 : usigma 146361946186458562560000 = 292723892372917125120000 := by
    have e : (146361946186458562560000 : ℕ) = 467610051713925120000 * 313 ^ 1 := by norm_num
    rw [e, usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num), h10]
    norm_num
  rw [h11]

lemma known_isUnitaryPerfect {n : ℕ} (hn : n ∈ knownUnitaryPerfect) : IsUnitaryPerfect n := by
  fin_cases hn
  · exact isUnitaryPerfect_six
  · exact isUnitaryPerfect_sixty
  · exact isUnitaryPerfect_ninety
  · exact isUnitaryPerfect_87360
  · exact isUnitaryPerfect_N5

/-! ## Every unitary perfect number is even -/

/-- Splitting `n > 1` at its least prime factor: `n = p ^ k * m` with `p ∤ m`, and
correspondingly `σ*(n) = (1 + p ^ k) σ*(m)`. -/
lemma usigma_split_minFac {n : ℕ} (hn : 1 < n) :
    ∃ k m : ℕ, k ≠ 0 ∧ ¬ n.minFac ∣ m ∧ n = n.minFac ^ k * m ∧
      usigma n = (1 + n.minFac ^ k) * usigma m := by
  have hn0 : n ≠ 0 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨k, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 n.minFac hp.ne_one
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hnm
    exact hpm (hnm ▸ Nat.minFac_dvd n)
  refine ⟨k, m, hk, hpm, hnm, ?_⟩
  have hcop : Nat.Coprime (n.minFac ^ k) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  conv_lhs => rw [hnm]
  rw [usigma_mul_of_coprime hcop, usigma_prime_pow hp hk]

lemma not_two_dvd_minFac_pow {n k : ℕ} (hodd : ¬ 2 ∣ n) : ¬ 2 ∣ n.minFac ^ k := by
  intro hdvd
  exact hodd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd).trans (Nat.minFac_dvd n))

/-- `σ*(n)` is even for every odd `n > 1`. -/
lemma two_dvd_usigma_of_one_lt {n : ℕ} (hn : 1 < n) (hodd : ¬ 2 ∣ n) : 2 ∣ usigma n := by
  obtain ⟨k, m, -, -, -, hval⟩ := usigma_split_minFac hn
  have hpodd : ¬ 2 ∣ n.minFac ^ k := not_two_dvd_minFac_pow hodd
  have h2a : 2 ∣ 1 + n.minFac ^ k := by omega
  exact hval ▸ h2a.mul_right _

/-- Every unitary perfect number is even. -/
theorem even_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  obtain ⟨hpos, hsum⟩ := h
  rw [even_iff_two_dvd]
  by_contra hodd
  -- `n = 1` is impossible since `σ*(1) = 1 ≠ 2`
  have hn1 : n ≠ 1 := by
    rintro rfl
    rw [usigma_one] at hsum
    omega
  have hn : 1 < n := by omega
  obtain ⟨k, m, hk, hpm, hnm, hval⟩ := usigma_split_minFac hn
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hpodd : ¬ 2 ∣ n.minFac ^ k := not_two_dvd_minFac_pow hodd
  have hpk1 : 1 < n.minFac ^ k := Nat.one_lt_pow hk hp.one_lt
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hnm
    omega
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm0) with hm1 | hm1
  · -- `n` is a prime power: `1 + p ^ k = 2 p ^ k` forces `p ^ k = 1`
    rw [← hm1, usigma_one, mul_one] at hval
    rw [← hm1, mul_one] at hnm
    omega
  · -- otherwise `4 ∣ σ*(n) = 2 n`, so `n` is even
    have hmn : m ∣ n := Dvd.intro_left _ hnm.symm
    have hmodd : ¬ 2 ∣ m := fun hdvd => hodd (hdvd.trans hmn)
    have h2a : 2 ∣ 1 + n.minFac ^ k := by omega
    have h2b : 2 ∣ usigma m := two_dvd_usigma_of_one_lt hm1 hmodd
    have h4 : 4 ∣ usigma n := by
      obtain ⟨a, ha⟩ := h2a
      obtain ⟨b, hb⟩ := h2b
      exact ⟨a * b, by rw [hval, ha, hb]; ring⟩
    rw [hsum] at h4
    omega

/-! ## The target statement -/

/-- The assertion that a sixth unitary perfect number exists, i.e. that there is a unitary
perfect number other than the five known ones. -/
def SixthExists : Prop := ∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect

/-- **Conditional reduction.** Unconditional existence of a sixth unitary perfect number is a
well-known open problem, so the target is proved here in reduced form: a sixth unitary perfect
number exists as soon as there is a unitary perfect number which either exceeds the largest
known one, `146361946186458562560000`, or is not divisible by `3` (all five known unitary
perfect numbers are multiples of `3`). -/
theorem SixthUnitaryPerfectExists
    (h : ∃ n, IsUnitaryPerfect n ∧ (146361946186458562560000 < n ∨ ¬ (3 ∣ n))) :
    SixthExists := by
  obtain ⟨n, hn, hcond⟩ := h
  refine ⟨n, hn, ?_⟩
  simp only [knownUnitaryPerfect, Finset.mem_insert, Finset.mem_singleton]
  rcases hcond with hgt | h3
  · push_neg
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  · rintro (rfl | rfl | rfl | rfl | rfl) <;> exact h3 (by norm_num)

end Brockian.UnitaryPerfect

