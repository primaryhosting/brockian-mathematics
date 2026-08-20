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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block above is repeated as a plain comment on the very first line of the
file; Lean requires `import` commands to precede any module docstring.)

## Contents

A *unitary divisor* of `n` is a divisor `d` with `gcd d (n / d) = 1`, and `n` is
*unitary perfect* when the sum `σ*(n)` of its unitary divisors equals `2 n`.
Exactly five unitary perfect numbers are known
(`6`, `60`, `90`, `87360`, `146361946186458562560000`), and whether a sixth one
exists is an open problem; consequently the target statement here is a
*conditional reduction* rather than an unconditional existence proof.

We develop:

* `sigmaStar_mul_of_coprime`: `σ*` is multiplicative on coprime arguments;
* `sigmaStar_prime_pow`: `σ*(p ^ a) = p ^ a + 1`;
* verification that each of the five known numbers is unitary perfect;
* `not_isUnitaryPerfect_of_odd`: there is no odd unitary perfect number;
* `SixthUnitaryPerfectExists`: if some unitary perfect number exceeds the largest
  known one, then a unitary perfect number outside the known five exists.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: divisors `d` of `n` with `gcd d (n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- `sigmaStar n = σ*(n)` is the sum of the unitary divisors of `n`. -/
def sigmaStar (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is unitary perfect when it is positive and `σ*(n) = 2 n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ sigmaStar n = 2 * n

/-- The five known unitary perfect numbers. -/
def knownUnitaryPerfect : Finset ℕ :=
  {6, 60, 90, 87360, 146361946186458562560000}

/-- The assertion that a sixth unitary perfect number exists, i.e. that some unitary
perfect number is not one of the five known ones. -/
def SixthUnitaryPerfect : Prop :=
  ∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect

theorem mem_unitaryDivisors {n d : ℕ} (hn : n ≠ 0) :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, hn]

theorem sigmaStar_one : sigmaStar 1 = 1 := by decide

/-- `σ*` is multiplicative on coprime arguments. -/
theorem sigmaStar_mul_of_coprime {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : Nat.Coprime u v) : sigmaStar (u * v) = sigmaStar u * sigmaStar v := by
  have huv : u * v ≠ 0 := mul_ne_zero hu hv
  rw [sigmaStar, sigmaStar, sigmaStar, Finset.sum_mul_sum, ← Finset.sum_product']
  refine (Finset.sum_nbij' (i := fun p => p.1 * p.2) (j := fun x => (Nat.gcd x u, Nat.gcd x v))
    ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨d, e⟩ hde
    simp only [Finset.mem_product] at hde
    obtain ⟨hd, he⟩ := hde
    rw [mem_unitaryDivisors hu] at hd
    rw [mem_unitaryDivisors hv] at he
    obtain ⟨hdu, hdc⟩ := hd
    obtain ⟨hev, hec⟩ := he
    rw [mem_unitaryDivisors huv]
    refine ⟨mul_dvd_mul hdu hev, ?_⟩
    rw [← Nat.div_mul_div_comm hdu hev]
    have h1 : Nat.Coprime d (v / e) :=
      (h.coprime_dvd_left hdu).coprime_dvd_right (Nat.div_dvd_of_dvd hev)
    have h2 : Nat.Coprime e (u / d) :=
      (h.symm.coprime_dvd_left hev).coprime_dvd_right (Nat.div_dvd_of_dvd hdu)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hdc h1) (Nat.Coprime.mul_right h2 hec)
  · intro x hx
    rw [mem_unitaryDivisors huv] at hx
    obtain ⟨hxd, hxc⟩ := hx
    have hxeq : Nat.gcd x u * Nat.gcd x v = x :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hxd
    have hdu : Nat.gcd x u ∣ u := Nat.gcd_dvd_right _ _
    have hev : Nat.gcd x v ∣ v := Nat.gcd_dvd_right _ _
    have hdiv : (u * v) / x = (u / Nat.gcd x u) * (v / Nat.gcd x v) := by
      have hc := Nat.div_mul_div_comm hdu hev
      rw [hxeq] at hc
      exact hc.symm
    rw [hdiv] at hxc
    simp only [Finset.mem_product]
    refine ⟨?_, ?_⟩
    · rw [mem_unitaryDivisors hu]
      exact ⟨hdu, (hxc.coprime_dvd_left (Dvd.intro _ hxeq)).coprime_dvd_right ⟨_, rfl⟩⟩
    · rw [mem_unitaryDivisors hv]
      exact ⟨hev, (hxc.coprime_dvd_left (Dvd.intro_left _ hxeq)).coprime_dvd_right
        ⟨_, mul_comm _ _⟩⟩
  · rintro ⟨d, e⟩ hde
    simp only [Finset.mem_product] at hde
    obtain ⟨hd, he⟩ := hde
    rw [mem_unitaryDivisors hu] at hd
    rw [mem_unitaryDivisors hv] at he
    have hdu : Nat.Coprime e u := h.symm.coprime_dvd_left he.1
    have hev : Nat.Coprime d v := h.coprime_dvd_left hd.1
    have h1 : Nat.gcd (d * e) u = d := by
      rw [Nat.Coprime.gcd_mul_right_cancel d hdu, Nat.gcd_eq_left hd.1]
    have h2 : Nat.gcd (d * e) v = e := by
      rw [Nat.Coprime.gcd_mul_left_cancel e hev, Nat.gcd_eq_left he.1]
    simp [h1, h2]
  · intro x hx
    rw [mem_unitaryDivisors huv] at hx
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hx.1
  · rintro ⟨d, e⟩ _
    rfl

/-- The unitary divisors of a prime power `p ^ a` are `1` and `p ^ a`. -/
theorem unitaryDivisors_prime_pow {p a : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ a) = {1, p ^ a} := by
  have hpa : p ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
  ext d
  rw [mem_unitaryDivisors hpa]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, hc⟩
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
    rw [Nat.pow_div hk hp.pos] at hc
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · left; simp [hk0]
    · right
      have hak : a - k = 0 := by
        by_contra hne
        have hp1 : p ∣ p ^ k := dvd_pow_self p (by omega)
        have hp2 : p ∣ p ^ (a - k) := dvd_pow_self p hne
        have hd1 : p ∣ 1 := hc ▸ Nat.dvd_gcd hp1 hp2
        exact absurd hp.one_lt (by have := Nat.le_of_dvd one_pos hd1; omega)
      congr 1
      omega
  · rintro (rfl | rfl)
    · exact ⟨one_dvd _, by simp⟩
    · refine ⟨dvd_rfl, ?_⟩
      rw [Nat.div_self (Nat.pos_of_ne_zero hpa)]
      exact Nat.coprime_one_right _

theorem sigmaStar_prime_pow {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) :
    sigmaStar (p ^ a) = p ^ a + 1 := by
  rw [sigmaStar, unitaryDivisors_prime_pow hp, Finset.sum_pair (Nat.one_lt_pow ha hp.one_lt).ne]
  omega

/-- Step lemma for evaluating `σ*` at an explicit factorization, one prime power at
a time. -/
theorem sigmaStar_step {p a m N S T : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hm : m ≠ 0)
    (hcop : Nat.Coprime (p ^ a) m) (hN : p ^ a * m = N) (hS : sigmaStar m = S)
    (hT : (p ^ a + 1) * S = T) : sigmaStar N = T := by
  subst hN; subst hS; subst hT
  rw [sigmaStar_mul_of_coprime (pow_ne_zero _ hp.ne_zero) hm hcop, sigmaStar_prime_pow hp ha]

theorem sigmaStar_six : sigmaStar 6 = 12 := by decide

theorem sigmaStar_sixty : sigmaStar 60 = 120 := by decide

theorem sigmaStar_ninety : sigmaStar 90 = 180 := by decide

theorem sigmaStar_87360 : sigmaStar 87360 = 174720 := by
  have h13 : sigmaStar 13 = 14 :=
    sigmaStar_step (p := 13) (a := 1) (m := 1) (by norm_num) one_ne_zero one_ne_zero
      (by norm_num) (by norm_num) sigmaStar_one (by norm_num)
  have h91 : sigmaStar 91 = 112 :=
    sigmaStar_step (p := 7) (a := 1) (m := 13) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h13 (by norm_num)
  have h455 : sigmaStar 455 = 672 :=
    sigmaStar_step (p := 5) (a := 1) (m := 91) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h91 (by norm_num)
  have h1365 : sigmaStar 1365 = 2688 :=
    sigmaStar_step (p := 3) (a := 1) (m := 455) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h455 (by norm_num)
  exact sigmaStar_step (p := 2) (a := 6) (m := 1365) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h1365 (by norm_num)

theorem sigmaStar_fifth : sigmaStar 146361946186458562560000 = 292723892372917125120000 := by
  have h313 : sigmaStar 313 = 314 :=
    sigmaStar_step (p := 313) (a := 1) (m := 1) (by norm_num) one_ne_zero one_ne_zero
      (by norm_num) (by norm_num) sigmaStar_one (by norm_num)
  have h157 : sigmaStar 49141 = 49612 :=
    sigmaStar_step (p := 157) (a := 1) (m := 313) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h313 (by norm_num)
  have h109 : sigmaStar 5356369 = 5457320 :=
    sigmaStar_step (p := 109) (a := 1) (m := 49141) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h157 (by norm_num)
  have h79 : sigmaStar 423153151 = 436585600 :=
    sigmaStar_step (p := 79) (a := 1) (m := 5356369) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h109 (by norm_num)
  have h37 : sigmaStar 15656666587 = 16590252800 :=
    sigmaStar_step (p := 37) (a := 1) (m := 423153151) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h79 (by norm_num)
  have h19 : sigmaStar 297476665153 = 331805056000 :=
    sigmaStar_step (p := 19) (a := 1) (m := 15656666587) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h37 (by norm_num)
  have h13 : sigmaStar 3867196646989 = 4645270784000 :=
    sigmaStar_step (p := 13) (a := 1) (m := 297476665153) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h19 (by norm_num)
  have h11 : sigmaStar 42539163116879 = 55743249408000 :=
    sigmaStar_step (p := 11) (a := 1) (m := 3867196646989) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h13 (by norm_num)
  have h7 : sigmaStar 297774141818153 = 445945995264000 :=
    sigmaStar_step (p := 7) (a := 1) (m := 42539163116879) (by norm_num) one_ne_zero (by norm_num)
      (by norm_num) (by norm_num) h11 (by norm_num)
  have h5 : sigmaStar 186108838636345625 = 279162193035264000 :=
    sigmaStar_step (p := 5) (a := 4) (m := 297774141818153) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h7 (by norm_num)
  have h3 : sigmaStar 558326515909036875 = 1116648772141056000 :=
    sigmaStar_step (p := 3) (a := 1) (m := 186108838636345625) (by norm_num) one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) h5 (by norm_num)
  exact sigmaStar_step (p := 2) (a := 18) (m := 558326515909036875) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h3 (by norm_num)

theorem isUnitaryPerfect_six : IsUnitaryPerfect 6 := ⟨by norm_num, sigmaStar_six⟩

theorem isUnitaryPerfect_sixty : IsUnitaryPerfect 60 := ⟨by norm_num, sigmaStar_sixty⟩

theorem isUnitaryPerfect_ninety : IsUnitaryPerfect 90 := ⟨by norm_num, sigmaStar_ninety⟩

theorem isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := ⟨by norm_num, sigmaStar_87360⟩

theorem isUnitaryPerfect_fifth : IsUnitaryPerfect 146361946186458562560000 :=
  ⟨by norm_num, by rw [sigmaStar_fifth]⟩

/-- Splitting off the largest power of the smallest prime factor. -/
theorem sigmaStar_minFac_split {n : ℕ} (hn : 1 < n) :
    sigmaStar n = (n.minFac ^ n.factorization n.minFac + 1) *
      sigmaStar (n / n.minFac ^ n.factorization n.minFac) := by
  have hn0 : n ≠ 0 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have ha : n.factorization n.minFac ≠ 0 := by
    have := (Nat.Prime.factorization_pos_of_dvd hp hn0 (Nat.minFac_dvd n))
    omega
  have hm : n / n.minFac ^ n.factorization n.minFac ≠ 0 :=
    (Nat.ordCompl_pos n.minFac hn0).ne'
  refine sigmaStar_step hp ha hm ?_ (Nat.ordProj_mul_ordCompl_eq_self n n.minFac) rfl rfl
  exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)

/-- For odd `n > 1`, the largest power of the smallest prime factor is odd. -/
theorem odd_ordProj_of_odd {n : ℕ} (hodd : Odd n) (hn : 1 < n) :
    Odd (n.minFac ^ n.factorization n.minFac) := by
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  refine Odd.pow ?_
  rcases hp.eq_two_or_odd' with h2 | hoddp
  · exfalso
    obtain ⟨c, hc⟩ : (2 : ℕ) ∣ n := by rw [← h2]; exact Nat.minFac_dvd n
    obtain ⟨t, ht⟩ := hodd
    omega
  · exact hoddp

/-- For odd `n > 1`, `σ*(n)` is even. -/
theorem even_sigmaStar_of_odd {n : ℕ} (hodd : Odd n) (hn : 1 < n) : Even (sigmaStar n) := by
  rw [sigmaStar_minFac_split hn]
  exact ((odd_ordProj_of_odd hodd hn).add_one).mul_right _

/-- There is no odd unitary perfect number. -/
theorem not_isUnitaryPerfect_of_odd {n : ℕ} (hodd : Odd n) : ¬ IsUnitaryPerfect n := by
  rintro ⟨hpos, hσ⟩
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hpos.ne') with h1 | hn
  · rw [← h1, sigmaStar_one] at hσ; omega
  have hn0 : n ≠ 0 := by omega
  obtain ⟨q, m, hq1, hmpos, hprod, hsplit, hqodd⟩ :
      ∃ q m : ℕ, 1 < q ∧ 0 < m ∧ q * m = n ∧ sigmaStar n = (q + 1) * sigmaStar m ∧ Odd q := by
    have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    have ha : n.factorization n.minFac ≠ 0 := by
      have := Nat.Prime.factorization_pos_of_dvd hp hn0 (Nat.minFac_dvd n)
      omega
    exact ⟨n.minFac ^ n.factorization n.minFac, n / n.minFac ^ n.factorization n.minFac,
      Nat.one_lt_pow ha hp.one_lt, Nat.ordCompl_pos _ hn0,
      Nat.ordProj_mul_ordCompl_eq_self n n.minFac, sigmaStar_minFac_split hn,
      odd_ordProj_of_odd hodd hn⟩
  have hmodd : Odd m := by
    rcases Nat.even_or_odd m with he | ho
    · exfalso
      obtain ⟨c, hc⟩ : (2 : ℕ) ∣ n := he.two_dvd.trans ⟨q, by rw [← hprod]; ring⟩
      obtain ⟨t, ht⟩ := hodd
      omega
    · exact ho
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hmpos.ne') with hm1 | hm1
  · -- `n` is a prime power: `q + 1 = 2 q` forces `q = 1`, contradicting `1 < q`
    rw [hsplit, ← hm1, sigmaStar_one, mul_one, ← hprod, ← hm1, mul_one] at hσ
    omega
  · -- otherwise `4 ∣ σ*(n) = 2 n`, forcing `n` to be even
    obtain ⟨k, hk⟩ := even_sigmaStar_of_odd hmodd hm1
    obtain ⟨j, hj⟩ := hqodd
    obtain ⟨t, ht⟩ := hodd
    obtain ⟨w, hw⟩ : ∃ w, 2 * n = 4 * w := ⟨(j + 1) * k, by rw [← hσ, hsplit, hk, hj]; ring⟩
    omega

/-- A unitary perfect number larger than the fourth known one and different from the
fifth known one witnesses a sixth unitary perfect number. -/
theorem sixthUnitaryPerfect_of_gt_87360 {n : ℕ} (hn : IsUnitaryPerfect n) (hlt : 87360 < n)
    (hne : n ≠ 146361946186458562560000) : SixthUnitaryPerfect := by
  refine ⟨n, hn, ?_⟩
  simp only [knownUnitaryPerfect, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨by omega, by omega, by omega, by omega, hne⟩

/-- **Conditional reduction (target).**
A sixth unitary perfect number exists — that is, some unitary perfect number is
not among the five known ones — provided that some unitary perfect number exceeds
the largest known one, `146361946186458562560000`.

Whether such a number exists is an open problem, so the statement is conditional;
the five known values are verified unconditionally above
(`isUnitaryPerfect_six`, ..., `isUnitaryPerfect_fifth`), and every unitary perfect
number is even (`not_isUnitaryPerfect_of_odd`). -/
theorem SixthUnitaryPerfectExists
    (h : ∃ n, IsUnitaryPerfect n ∧ 146361946186458562560000 < n) :
    SixthUnitaryPerfect := by
  obtain ⟨n, hn, hlt⟩ := h
  exact sixthUnitaryPerfect_of_gt_87360 hn (by omega) (by omega)

end Brockian.UnitaryPerfect

