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

open Finset

namespace Brockian.UnitaryPerfect

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- `sigmaStar n` (usually written `σ*(n)`) is the sum of the unitary divisors of `n`. -/
def sigmaStar (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is unitary perfect if it is positive and the sum of its unitary divisors is `2 * n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ sigmaStar n = 2 * n

/-- The five known unitary perfect numbers. -/
def knownUnitaryPerfect : Finset ℕ := {6, 60, 90, 87360, 146361946186458562560000}

/-! ### Basic facts about unitary divisors -/

theorem mem_unitaryDivisors {n d : ℕ} (hn : n ≠ 0) :
    d ∈ unitaryDivisors n ↔ ∃ e, n = d * e ∧ Nat.Coprime d e := by
  simp only [unitaryDivisors, mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hc⟩
    exact ⟨n / d, (Nat.mul_div_cancel' hd).symm, hc⟩
  · rintro ⟨e, rfl, hc⟩
    have hd : d ≠ 0 := by rintro rfl; simp at hn
    refine ⟨⟨Dvd.intro e rfl, hn⟩, ?_⟩
    rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)]

theorem dvd_of_mem_unitaryDivisors {n d : ℕ} (h : d ∈ unitaryDivisors n) : d ∣ n := by
  simp only [unitaryDivisors, mem_filter, Nat.mem_divisors] at h
  exact h.1.1

@[simp] theorem sigmaStar_one : sigmaStar 1 = 1 := by
  decide

@[simp] theorem sigmaStar_zero : sigmaStar 0 = 0 := by
  simp [sigmaStar, unitaryDivisors]

/-- The sum-of-unitary-divisors function is multiplicative. -/
theorem sigmaStar_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigmaStar (m * n) = sigmaStar m * sigmaStar n := by
  rcases eq_or_ne m 0 with rfl | hm
  · have : n = 1 := by simpa using h
    subst this
    simp
  rcases eq_or_ne n 0 with rfl | hn
  · have : m = 1 := by simpa using h
    subst this
    simp
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [sigmaStar, sigmaStar, sigmaStar, Finset.sum_mul_sum, ← Finset.sum_product']
  refine (Finset.sum_nbij' (i := fun x : ℕ × ℕ => x.1 * x.2)
    (j := fun d => (Nat.gcd d m, Nat.gcd d n)) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product] at hab
    obtain ⟨ha, hb⟩ := hab
    obtain ⟨e1, he1, hc1⟩ := (mem_unitaryDivisors hm).1 ha
    obtain ⟨e2, he2, hc2⟩ := (mem_unitaryDivisors hn).1 hb
    have hdam : a ∣ m := dvd_of_mem_unitaryDivisors ha
    have hdbn : b ∣ n := dvd_of_mem_unitaryDivisors hb
    have he1m : e1 ∣ m := Dvd.intro_left _ he1.symm
    have he2n : e2 ∣ n := Dvd.intro_left _ he2.symm
    refine (mem_unitaryDivisors hmn).2 ⟨e1 * e2, by rw [he1, he2]; ring, ?_⟩
    have hae2 : Nat.Coprime a e2 :=
      Nat.Coprime.coprime_dvd_right he2n (Nat.Coprime.coprime_dvd_left hdam h)
    have hbe1 : Nat.Coprime b e1 :=
      Nat.Coprime.coprime_dvd_right he1m (Nat.Coprime.coprime_dvd_left hdbn h.symm)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hc1 hae2) (Nat.Coprime.mul_right hbe1 hc2)
  · intro d hd
    obtain ⟨e, he, hc⟩ := (mem_unitaryDivisors hmn).1 hd
    have hdvd : d ∣ m * n := Dvd.intro e he.symm
    have hgcd : Nat.gcd d m * Nat.gcd d n = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hdvd
    set a := Nat.gcd d m with ha
    set b := Nat.gcd d n with hb
    have ham : a ∣ m := Nat.gcd_dvd_right _ _
    have hbn : b ∣ n := Nat.gcd_dvd_right _ _
    obtain ⟨m', hm'⟩ := id ham
    obtain ⟨n', hn'⟩ := id hbn
    have hae : Nat.Coprime a e := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hc
    have hbe : Nat.Coprime b e := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hc
    have ha0 : a ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hm'
      exact hm hm'
    have hb0 : b ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hn'
      exact hn hn'
    have key1 : m' * n = b * e := by
      refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha0) ?_
      calc a * (m' * n) = (a * m') * n := by ring
        _ = m * n := by rw [← hm']
        _ = d * e := he
        _ = a * (b * e) := by rw [← hgcd]; ring
    have key2 : n' * m = a * e := by
      refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hb0) ?_
      calc b * (n' * m) = (b * n') * m := by ring
        _ = n * m := by rw [← hn']
        _ = m * n := by ring
        _ = d * e := he
        _ = b * (a * e) := by rw [← hgcd]; ring
    have hm'b : Nat.Coprime m' b :=
      Nat.Coprime.coprime_dvd_right hbn (Nat.Coprime.coprime_dvd_left ⟨a, by rw [hm']; ring⟩ h)
    have hn'a : Nat.Coprime n' a :=
      Nat.Coprime.coprime_dvd_right ham (Nat.Coprime.coprime_dvd_left ⟨b, by rw [hn']; ring⟩ h.symm)
    have hm'e : m' ∣ e := hm'b.dvd_of_dvd_mul_left ⟨n, key1.symm⟩
    have hn'e : n' ∣ e := hn'a.dvd_of_dvd_mul_left ⟨m, key2.symm⟩
    simp only [Finset.mem_product]
    exact ⟨(mem_unitaryDivisors hm).2 ⟨m', hm', Nat.Coprime.coprime_dvd_right hm'e hae⟩,
      (mem_unitaryDivisors hn).2 ⟨n', hn', Nat.Coprime.coprime_dvd_right hn'e hbe⟩⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product] at hab
    obtain ⟨ha, hb⟩ := hab
    have ham : a ∣ m := dvd_of_mem_unitaryDivisors ha
    have hbn : b ∣ n := dvd_of_mem_unitaryDivisors hb
    have hbm : Nat.Coprime b m := Nat.Coprime.coprime_dvd_left hbn h.symm
    have han : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left ham h
    have h1 : Nat.gcd (a * b) m = a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a hbm]
      exact Nat.gcd_eq_left ham
    have h2 : Nat.gcd (a * b) n = b := by
      rw [mul_comm, Nat.Coprime.gcd_mul_right_cancel b han]
      exact Nat.gcd_eq_left hbn
    simp [h1, h2]
  · intro d hd
    obtain ⟨e, he, hc⟩ := (mem_unitaryDivisors hmn).1 hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr (Dvd.intro e he.symm)
  · rintro ⟨a, b⟩ _
    rfl

theorem unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  have hp0 : p ≠ 0 := hp.pos.ne'
  ext d
  rw [mem_unitaryDivisors (pow_ne_zero _ hp0)]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨e, he, hc⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 ⟨e, he⟩
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ he.symm)
    have hk' : k = i + j := by
      have : p ^ k = p ^ (i + j) := by rw [pow_add]; exact he
      exact Nat.pow_right_injective hp.two_le this
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · left; simp
    · have hj0 : j = 0 := by
        by_contra hj0
        have h1 : p ∣ p ^ i := dvd_pow_self p hipos.ne'
        have h2 : p ∣ p ^ j := dvd_pow_self p hj0
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h2)
      subst hj0
      right
      simp [hk']
  · rintro (rfl | rfl)
    · exact ⟨p ^ k, by simp, by simp⟩
    · exact ⟨1, by simp, by simp⟩

theorem sigmaStar_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    sigmaStar (p ^ k) = 1 + p ^ k := by
  have hne : (1 : ℕ) ≠ p ^ k := by
    have : 1 < p ^ k := Nat.one_lt_pow hk hp.one_lt
    omega
  rw [sigmaStar, unitaryDivisors_prime_pow hp, Finset.sum_insert (by simpa using hne),
    Finset.sum_singleton]

/-- The product formula for the sum-of-unitary-divisors function. -/
theorem sigmaStar_eq_prod {n : ℕ} (hn : n ≠ 0) :
    sigmaStar n = ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [Nat.multiplicative_factorization sigmaStar (fun _ _ hxy => sigmaStar_mul_of_coprime hxy)
    sigmaStar_one hn, Finsupp.prod]
  refine Finset.prod_congr n.support_factorization fun p hp => ?_
  exact sigmaStar_prime_pow (Nat.prime_of_mem_primeFactors hp)
    (by simpa using (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn
      (Nat.dvd_of_mem_primeFactors hp)).ne')

theorem prod_primeFactors_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-! ### The five known unitary perfect numbers -/

theorem isUnitaryPerfect_six : IsUnitaryPerfect 6 := by
  refine ⟨by norm_num, ?_⟩
  have h : (6 : ℕ) = 2 ^ 1 * 3 ^ 1 := by norm_num
  rw [h, sigmaStar_mul_of_coprime (by norm_num), sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero]
  norm_num

theorem isUnitaryPerfect_sixty : IsUnitaryPerfect 60 := by
  refine ⟨by norm_num, ?_⟩
  have h : (60 : ℕ) = 2 ^ 2 * (3 ^ 1 * 5 ^ 1) := by norm_num
  rw [h, sigmaStar_mul_of_coprime (by norm_num), sigmaStar_mul_of_coprime (by norm_num),
    sigmaStar_prime_pow (by norm_num) two_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero]
  norm_num

theorem isUnitaryPerfect_ninety : IsUnitaryPerfect 90 := by
  refine ⟨by norm_num, ?_⟩
  have h : (90 : ℕ) = 2 ^ 1 * (3 ^ 2 * 5 ^ 1) := by norm_num
  rw [h, sigmaStar_mul_of_coprime (by norm_num), sigmaStar_mul_of_coprime (by norm_num),
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) two_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero]
  norm_num

theorem isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  refine ⟨by norm_num, ?_⟩
  have h : (87360 : ℕ) = 2 ^ 6 * (3 ^ 1 * (5 ^ 1 * (7 ^ 1 * 13 ^ 1))) := by norm_num
  rw [h, sigmaStar_mul_of_coprime (by norm_num), sigmaStar_mul_of_coprime (by norm_num),
    sigmaStar_mul_of_coprime (by norm_num), sigmaStar_mul_of_coprime (by norm_num),
    sigmaStar_prime_pow (by norm_num) (by norm_num),
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero]
  norm_num

theorem isUnitaryPerfect_big : IsUnitaryPerfect 146361946186458562560000 := by
  refine ⟨by norm_num, ?_⟩
  have h : (146361946186458562560000 : ℕ) =
      2 ^ 18 * (3 ^ 1 * (5 ^ 4 * (7 ^ 1 * (11 ^ 1 * (13 ^ 1 * (19 ^ 1 * (37 ^ 1 *
        (79 ^ 1 * (109 ^ 1 * (157 ^ 1 * 313 ^ 1)))))))))) := by norm_num
  rw [h, sigmaStar_mul_of_coprime (by norm_num), sigmaStar_mul_of_coprime (by norm_num),
    sigmaStar_mul_of_coprime (by norm_num), sigmaStar_mul_of_coprime (by norm_num),
    sigmaStar_mul_of_coprime (by norm_num), sigmaStar_mul_of_coprime (by norm_num),
    sigmaStar_mul_of_coprime (by norm_num), sigmaStar_mul_of_coprime (by norm_num),
    sigmaStar_mul_of_coprime (by norm_num), sigmaStar_mul_of_coprime (by norm_num),
    sigmaStar_mul_of_coprime (by norm_num),
    sigmaStar_prime_pow (by norm_num) (by norm_num),
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) (by norm_num),
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero,
    sigmaStar_prime_pow (by norm_num) one_ne_zero]
  norm_num

/-- The known list really consists of five distinct numbers. -/
theorem card_knownUnitaryPerfect : knownUnitaryPerfect.card = 5 := by
  decide

/-- All five known unitary perfect numbers really are unitary perfect. -/
theorem knownUnitaryPerfect_isUnitaryPerfect :
    ∀ n ∈ knownUnitaryPerfect, IsUnitaryPerfect n := by
  intro n hn
  simp only [knownUnitaryPerfect, mem_insert, mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact isUnitaryPerfect_six
  · exact isUnitaryPerfect_sixty
  · exact isUnitaryPerfect_ninety
  · exact isUnitaryPerfect_87360
  · exact isUnitaryPerfect_big

/-! ### Structure of any unitary perfect number -/

/-- A unitary perfect number has at least two distinct prime factors. -/
theorem two_le_card_primeFactors {n : ℕ} (hn : IsUnitaryPerfect n) :
    2 ≤ n.primeFactors.card := by
  obtain ⟨hpos, hper⟩ := hn
  have hn0 : n ≠ 0 := hpos.ne'
  by_contra hcard
  push_neg at hcard
  interval_cases hc : n.primeFactors.card
  · have : n.primeFactors = ∅ := Finset.card_eq_zero.1 hc
    have hn1 : n = 1 := by
      rcases Nat.primeFactors_eq_empty.1 this with h | h
      · exact absurd h hn0
      · exact h
    rw [hn1] at hper
    simp at hper
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hc
    have hval : n = p ^ n.factorization p := by
      have := prod_primeFactors_pow_factorization hn0
      rw [hp, Finset.prod_singleton] at this
      exact this.symm
    have hsig : sigmaStar n = 1 + p ^ n.factorization p := by
      rw [sigmaStar_eq_prod hn0, hp, Finset.prod_singleton]
    have hkey : 1 + p ^ n.factorization p = 2 * n := by rw [← hsig, hper]
    have hn1 : n = 1 := by omega
    rw [hn1] at hc
    simp at hc

/-- Subbarao's observation: every unitary perfect number is even. -/
theorem even_of_isUnitaryPerfect {n : ℕ} (hn : IsUnitaryPerfect n) : Even n := by
  obtain ⟨hpos, hper⟩ := hn
  have hn0 : n ≠ 0 := hpos.ne'
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1
    (two_le_card_primeFactors ⟨hpos, hper⟩)
  have hodd_of_mem : ∀ r ∈ n.primeFactors, 2 ∣ 1 + r ^ n.factorization r := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrn : r ∣ n := Nat.dvd_of_mem_primeFactors hr
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrn)
    have hrodd : Odd r := hrp.odd_of_ne_two hr2
    have : Odd (r ^ n.factorization r) := hrodd.pow
    obtain ⟨t, ht⟩ := this
    exact ⟨t + 1, by omega⟩
  have hq' : q ∈ n.primeFactors.erase p := Finset.mem_erase.2 ⟨hpq.symm, hq⟩
  have hsplit : ∏ r ∈ n.primeFactors, (1 + r ^ n.factorization r) =
      (1 + p ^ n.factorization p) * ((1 + q ^ n.factorization q) *
        ∏ r ∈ (n.primeFactors.erase p).erase q, (1 + r ^ n.factorization r)) := by
    rw [← Finset.mul_prod_erase _ (fun r => 1 + r ^ n.factorization r) hp,
      ← Finset.mul_prod_erase _ (fun r => 1 + r ^ n.factorization r) hq']
  have h4 : 4 ∣ sigmaStar n := by
    rw [sigmaStar_eq_prod hn0, hsplit]
    obtain ⟨s, hs⟩ := hodd_of_mem p hp
    obtain ⟨t, ht⟩ := hodd_of_mem q hq
    refine ⟨s * (t * ∏ r ∈ (n.primeFactors.erase p).erase q, (1 + r ^ n.factorization r)), ?_⟩
    rw [hs, ht]
    ring
  rw [hper] at h4
  obtain ⟨c, hc⟩ := h4
  exact (Nat.not_even_iff_odd.2 hodd) ⟨c, by omega⟩

/-- If `n` is unitary perfect and `2 ^ a` is the exact power of `2` dividing `n`, then
`1 + 2 ^ a` divides the odd part `n / 2 ^ a` of `n`. -/
theorem one_add_two_pow_dvd_oddPart {n : ℕ} (hn : IsUnitaryPerfect n) :
    (1 + 2 ^ n.factorization 2) ∣ n / 2 ^ n.factorization 2 := by
  obtain ⟨hpos, hper⟩ := hn
  have hn0 : n ≠ 0 := hpos.ne'
  have heven : Even n := even_of_isUnitaryPerfect ⟨hpos, hper⟩
  set a := n.factorization 2 with ha
  set m := n / 2 ^ a with hm
  have hsplit : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hn0)
  have hapos : a ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 heven.two_dvd).ne'
  have hsig : (1 + 2 ^ a) * sigmaStar m = 2 * n := by
    rw [← sigmaStar_prime_pow Nat.prime_two hapos, ← sigmaStar_mul_of_coprime hcop, hsplit, hper]
  have hdvd : (1 + 2 ^ a) ∣ 2 ^ (a + 1) * m := by
    refine ⟨sigmaStar m, ?_⟩
    calc 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by ring
      _ = 2 * n := by rw [hsplit]
      _ = (1 + 2 ^ a) * sigmaStar m := hsig.symm
  have hodd : Odd (1 + 2 ^ a) := by
    have : Even (2 ^ a) := (Nat.even_pow' hapos).2 even_two
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by omega⟩
  have hcop2 : Nat.Coprime (1 + 2 ^ a) (2 ^ (a + 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  exact hcop2.dvd_of_dvd_mul_left hdvd

/-! ### The main (conditional) statement -/

/-- **A sixth unitary perfect number.**  Whether a unitary perfect number other than the five
known ones (`6`, `60`, `90`, `87360`, `146361946186458562560000`) exists is an open problem, so
what is proved here is a conditional reduction: a sixth unitary perfect number exists if and
only if there is a unitary perfect number outside the known list, and any such number is
necessarily even, has at least two distinct prime factors, and its odd part is divisible by
`1 + 2 ^ a`, where `2 ^ a` is the exact power of `2` dividing it. -/
theorem SixthUnitaryPerfectExists :
    (∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect) ↔
      (∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect ∧ Even n ∧
        2 ≤ n.primeFactors.card ∧
        (1 + 2 ^ n.factorization 2) ∣ n / 2 ^ n.factorization 2) := by
  constructor
  · rintro ⟨n, hn, hnk⟩
    exact ⟨n, hn, hnk, even_of_isUnitaryPerfect hn, two_le_card_primeFactors hn,
      one_add_two_pow_dvd_oddPart hn⟩
  · rintro ⟨n, hn, hnk, -, -, -⟩
    exact ⟨n, hn, hnk⟩

end Brockian.UnitaryPerfect

