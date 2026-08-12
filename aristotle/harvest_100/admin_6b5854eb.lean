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

(The header above is repeated here as a module docstring: Lean requires all
`import` statements to precede any module documentation comment.)

## Contents

A *unitary divisor* of `n` is a divisor `d` with `gcd (d, n/d) = 1`, and `n` is
*unitary perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.
Only five unitary perfect numbers are known, and whether a sixth exists is open.

This file develops the basic theory (`σ*` is multiplicative, its value on prime
powers, and hence the product formula `σ*(n) = ∏_{p^a ‖ n} (p^a + 1)`), verifies
the five classically known unitary perfect numbers, proves the partial result
that no odd number is unitary perfect, and finally states and proves the
conditional reduction `SixthUnitaryPerfectExists`: as soon as there is *one*
unitary perfect number outside the known list of five, there are at least six
unitary perfect numbers.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => Nat.Coprime d (n / d)

/-- The sum-of-unitary-divisors function `σ*`. -/
def usigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is unitary perfect if it is positive and `σ*(n) = 2 * n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ usigma n = 2 * n

theorem mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ n ≠ 0 ∧ ∃ e, n = d * e ∧ Nat.Coprime d e := by
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, hn⟩, hc⟩
    exact ⟨hn, n / d, (Nat.mul_div_cancel' hd).symm, hc⟩
  · rintro ⟨hn, e, rfl, hc⟩
    have hd : d ≠ 0 := by rintro rfl; simp at hn
    refine ⟨⟨Dvd.intro e rfl, hn⟩, ?_⟩
    rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)]

theorem usigma_zero : usigma 0 = 0 := by
  simp [usigma, unitaryDivisors]

theorem usigma_one : usigma 1 = 1 := by
  have h : unitaryDivisors 1 = {1} := by decide
  simp [usigma, h]

/-- A divisor `a` of a coprime product splits as `gcd a m * gcd a n`. -/
theorem gcd_mul_gcd_of_dvd_mul {m n a : ℕ} (h : Nat.Coprime m n) (ha : a ∣ m * n) :
    Nat.gcd a m * Nat.gcd a n = a := by
  rw [← Nat.Coprime.gcd_mul a h, Nat.gcd_eq_left ha]

theorem gcd_mem_unitaryDivisors_left {m n a : ℕ} (h : Nat.Coprime m n)
    (ha : a ∈ unitaryDivisors (m * n)) : Nat.gcd a m ∈ unitaryDivisors m := by
  obtain ⟨hmn, f, hf, hcf⟩ := mem_unitaryDivisors.1 ha
  have hm : m ≠ 0 := fun h0 => hmn (by simp [h0])
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hf; exact hmn hf
  have hsplit : a = Nat.gcd a m * Nat.gcd a n :=
    (gcd_mul_gcd_of_dvd_mul h ⟨f, hf⟩).symm
  set a₁ := Nat.gcd a m with ha₁
  set a₂ := Nat.gcd a n with ha₂
  obtain ⟨m₁, hm₁⟩ : a₁ ∣ m := Nat.gcd_dvd_right a m
  obtain ⟨n₁, hn₁⟩ : a₂ ∣ n := Nat.gcd_dvd_right a n
  have hmul : a * f = a * (m₁ * n₁) := by
    conv_rhs => rw [hsplit]
    rw [← hf, hm₁, hn₁]; ring
  have hfe : f = m₁ * n₁ := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha0) hmul
  refine mem_unitaryDivisors.2 ⟨hm, m₁, hm₁, ?_⟩
  exact Nat.Coprime.coprime_dvd_right ⟨n₁, hfe⟩
    (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left a m) hcf)

/-- `σ*` is multiplicative. -/
theorem usigma_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at h; subst h; simp [usigma_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at h; subst h; simp [usigma_zero]
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun d => (Nat.gcd d m, Nat.gcd d n))
    (j := fun x => x.1 * x.2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    refine Finset.mem_product.2 ⟨gcd_mem_unitaryDivisors_left h ha,
      gcd_mem_unitaryDivisors_left h.symm ?_⟩
    rwa [mul_comm]
  · rintro ⟨a₁, a₂⟩ hx
    rw [Finset.mem_product] at hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨-, m₁, hm₁, hc₁⟩ := mem_unitaryDivisors.1 hx1
    obtain ⟨-, n₁, hn₁, hc₂⟩ := mem_unitaryDivisors.1 hx2
    have hd1 : a₁ ∣ m := ⟨m₁, hm₁⟩
    have hd2 : a₂ ∣ n := ⟨n₁, hn₁⟩
    have he1 : m₁ ∣ m := ⟨a₁, by rw [hm₁]; ring⟩
    have he2 : n₁ ∣ n := ⟨a₂, by rw [hn₁]; ring⟩
    refine mem_unitaryDivisors.2 ⟨hmn, m₁ * n₁, by rw [hm₁, hn₁]; ring, ?_⟩
    have c12 : Nat.Coprime a₁ n₁ :=
      Nat.Coprime.coprime_dvd_right he2 (Nat.Coprime.coprime_dvd_left hd1 h)
    have c21 : Nat.Coprime a₂ m₁ :=
      Nat.Coprime.coprime_dvd_right he1 (Nat.Coprime.coprime_dvd_left hd2 h.symm)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hc₁ c12)
      (Nat.Coprime.mul_right c21 hc₂)
  · intro a ha
    obtain ⟨-, e, he, -⟩ := mem_unitaryDivisors.1 ha
    exact gcd_mul_gcd_of_dvd_mul h ⟨e, he⟩
  · rintro ⟨a₁, a₂⟩ hx
    rw [Finset.mem_product] at hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨-, m₁, hm₁, -⟩ := mem_unitaryDivisors.1 hx1
    obtain ⟨-, n₁, hn₁, -⟩ := mem_unitaryDivisors.1 hx2
    have hd1 : a₁ ∣ m := ⟨m₁, hm₁⟩
    have hd2 : a₂ ∣ n := ⟨n₁, hn₁⟩
    have ca2m : Nat.Coprime a₂ m := Nat.Coprime.coprime_dvd_left hd2 h.symm
    have ca1n : Nat.Coprime a₁ n := Nat.Coprime.coprime_dvd_left hd1 h
    have e1 : Nat.gcd (a₁ * a₂) m = a₁ := by
      rw [Nat.Coprime.gcd_mul_right_cancel a₁ ca2m, Nat.gcd_eq_left hd1]
    have e2 : Nat.gcd (a₁ * a₂) n = a₂ := by
      rw [Nat.Coprime.gcd_mul_left_cancel a₂ ca1n, Nat.gcd_eq_left hd2]
    simp [e1, e2]
  · intro a ha
    obtain ⟨-, e, he, -⟩ := mem_unitaryDivisors.1 ha
    exact (gcd_mul_gcd_of_dvd_mul h ⟨e, he⟩).symm

theorem unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  have hp1 : 1 < p := hp.one_lt
  ext d
  rw [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨-, e, he, hc⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 ⟨e, he⟩
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · left; simp
    right
    have hei : e = p ^ (k - i) := by
      have hsplit : p ^ k = p ^ i * p ^ (k - i) := by
        rw [← pow_add]; congr 1; omega
      have hpi : 0 < p ^ i := pow_pos (by omega) i
      exact (Nat.eq_of_mul_eq_mul_left hpi (by rw [← he, hsplit])).symm
    subst hei
    have hnd : ¬ (p ∣ p ^ (k - i)) := by
      intro hd
      have hpi : p ∣ p ^ i := dvd_pow_self p (by omega)
      have h1 : p ∣ 1 := hc ▸ Nat.dvd_gcd hpi hd
      have := Nat.le_of_dvd one_pos h1
      omega
    have hki : k - i = 0 := by
      by_contra hne
      exact hnd (dvd_pow_self p hne)
    congr 1; omega
  · rintro (rfl | rfl)
    · exact ⟨by positivity, p ^ k, by ring, Nat.coprime_one_left _⟩
    · exact ⟨by positivity, 1, by ring, Nat.coprime_one_right _⟩

theorem usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    usigma (p ^ k) = p ^ k + 1 := by
  have hpk : 1 < p ^ k := Nat.one_lt_pow hk hp.one_lt
  rw [usigma, unitaryDivisors_prime_pow hp, Finset.sum_pair (by omega)]
  omega

/-- The product formula `σ*(n) = ∏_{p^a ‖ n} (p^a + 1)`. -/
theorem usigma_eq_factorization_prod {n : ℕ} (hn : n ≠ 0) :
    usigma n = n.factorization.prod fun p k => p ^ k + 1 := by
  rw [Nat.multiplicative_factorization usigma (fun _ _ h => usigma_mul_of_coprime h)
    usigma_one hn]
  refine Finsupp.prod_congr ?_
  intro p hp
  have hp' : p ∈ n.primeFactors := by rwa [Nat.support_factorization] at hp
  exact usigma_prime_pow (Nat.prime_of_mem_primeFactors hp') (Finsupp.mem_support_iff.1 hp)

/-- A convenient one-step rule for evaluating `σ*` along an explicit factorization. -/
theorem usigma_step {p k m n s v : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hc : Nat.Coprime (p ^ k) m) (hm : usigma m = s) (heq : p ^ k * m = n)
    (hv : (p ^ k + 1) * s = v) : usigma n = v := by
  subst heq; subst hv; subst hm
  rw [usigma_mul_of_coprime hc, usigma_prime_pow hp hk]

/-! ## The five known unitary perfect numbers -/

theorem usigma_three : usigma 3 = 4 :=
  usigma_step (p := 3) (k := 1) (m := 1) (by norm_num) one_ne_zero (by norm_num)
    usigma_one (by norm_num) (by norm_num)

theorem usigma_five : usigma 5 = 6 :=
  usigma_step (p := 5) (k := 1) (m := 1) (by norm_num) one_ne_zero (by norm_num)
    usigma_one (by norm_num) (by norm_num)

theorem usigma_six : usigma 6 = 12 :=
  usigma_step (p := 2) (k := 1) (m := 3) (by norm_num) one_ne_zero (by norm_num)
    usigma_three (by norm_num) (by norm_num)

theorem unitaryPerfect_six : IsUnitaryPerfect 6 := ⟨by norm_num, by rw [usigma_six]⟩

theorem usigma_fifteen : usigma 15 = 24 :=
  usigma_step (p := 3) (k := 1) (m := 5) (by norm_num) one_ne_zero (by norm_num)
    usigma_five (by norm_num) (by norm_num)

theorem usigma_sixty : usigma 60 = 120 :=
  usigma_step (p := 2) (k := 2) (m := 15) (by norm_num) two_ne_zero (by norm_num)
    usigma_fifteen (by norm_num) (by norm_num)

theorem unitaryPerfect_sixty : IsUnitaryPerfect 60 := ⟨by norm_num, by rw [usigma_sixty]⟩

theorem usigma_45 : usigma 45 = 60 :=
  usigma_step (p := 3) (k := 2) (m := 5) (by norm_num) two_ne_zero (by norm_num)
    usigma_five (by norm_num) (by norm_num)

theorem usigma_ninety : usigma 90 = 180 :=
  usigma_step (p := 2) (k := 1) (m := 45) (by norm_num) one_ne_zero (by norm_num)
    usigma_45 (by norm_num) (by norm_num)

theorem unitaryPerfect_ninety : IsUnitaryPerfect 90 := ⟨by norm_num, by rw [usigma_ninety]⟩

theorem usigma_87360 : usigma 87360 = 174720 := by
  have h13 : usigma 13 = 14 :=
    usigma_step (p := 13) (k := 1) (m := 1) (by norm_num) one_ne_zero (by norm_num)
      usigma_one (by norm_num) (by norm_num)
  have h91 : usigma 91 = 112 :=
    usigma_step (p := 7) (k := 1) (m := 13) (by norm_num) one_ne_zero (by norm_num)
      h13 (by norm_num) (by norm_num)
  have h455 : usigma 455 = 672 :=
    usigma_step (p := 5) (k := 1) (m := 91) (by norm_num) one_ne_zero (by norm_num)
      h91 (by norm_num) (by norm_num)
  have h1365 : usigma 1365 = 2688 :=
    usigma_step (p := 3) (k := 1) (m := 455) (by norm_num) one_ne_zero (by norm_num)
      h455 (by norm_num) (by norm_num)
  exact usigma_step (p := 2) (k := 6) (m := 1365) (by norm_num) (by norm_num) (by norm_num)
    h1365 (by norm_num) (by norm_num)

theorem unitaryPerfect_87360 : IsUnitaryPerfect 87360 := ⟨by norm_num, by rw [usigma_87360]⟩

theorem usigma_fifth : usigma 146361946186458562560000 = 292723892372917125120000 := by
  have h1 : usigma 313 = 314 :=
    usigma_step (p := 313) (k := 1) (m := 1) (by norm_num) one_ne_zero (by norm_num)
      usigma_one (by norm_num) (by norm_num)
  have h2 : usigma 49141 = 49612 :=
    usigma_step (p := 157) (k := 1) (m := 313) (by norm_num) one_ne_zero (by norm_num)
      h1 (by norm_num) (by norm_num)
  have h3 : usigma 5356369 = 5457320 :=
    usigma_step (p := 109) (k := 1) (m := 49141) (by norm_num) one_ne_zero (by norm_num)
      h2 (by norm_num) (by norm_num)
  have h4 : usigma 423153151 = 436585600 :=
    usigma_step (p := 79) (k := 1) (m := 5356369) (by norm_num) one_ne_zero (by norm_num)
      h3 (by norm_num) (by norm_num)
  have h5 : usigma 15656666587 = 16590252800 :=
    usigma_step (p := 37) (k := 1) (m := 423153151) (by norm_num) one_ne_zero (by norm_num)
      h4 (by norm_num) (by norm_num)
  have h6 : usigma 297476665153 = 331805056000 :=
    usigma_step (p := 19) (k := 1) (m := 15656666587) (by norm_num) one_ne_zero (by norm_num)
      h5 (by norm_num) (by norm_num)
  have h7 : usigma 3867196646989 = 4645270784000 :=
    usigma_step (p := 13) (k := 1) (m := 297476665153) (by norm_num) one_ne_zero (by norm_num)
      h6 (by norm_num) (by norm_num)
  have h8 : usigma 42539163116879 = 55743249408000 :=
    usigma_step (p := 11) (k := 1) (m := 3867196646989) (by norm_num) one_ne_zero (by norm_num)
      h7 (by norm_num) (by norm_num)
  have h9 : usigma 297774141818153 = 445945995264000 :=
    usigma_step (p := 7) (k := 1) (m := 42539163116879) (by norm_num) one_ne_zero (by norm_num)
      h8 (by norm_num) (by norm_num)
  have h10 : usigma 186108838636345625 = 279162193035264000 :=
    usigma_step (p := 5) (k := 4) (m := 297774141818153) (by norm_num) (by norm_num)
      (by norm_num) h9 (by norm_num) (by norm_num)
  have h11 : usigma 558326515909036875 = 1116648772141056000 :=
    usigma_step (p := 3) (k := 1) (m := 186108838636345625) (by norm_num) one_ne_zero
      (by norm_num) h10 (by norm_num) (by norm_num)
  exact usigma_step (p := 2) (k := 18) (m := 558326515909036875) (by norm_num) (by norm_num)
    (by norm_num) h11 (by norm_num) (by norm_num)

theorem unitaryPerfect_fifth : IsUnitaryPerfect 146361946186458562560000 :=
  ⟨by norm_num, by rw [usigma_fifth]⟩

/-- The five classically known unitary perfect numbers. -/
def knownFive : Finset ℕ := {6, 60, 90, 87360, 146361946186458562560000}

theorem knownFive_card : knownFive.card = 5 := by decide

theorem knownFive_unitaryPerfect : ∀ m ∈ knownFive, IsUnitaryPerfect m := by
  intro m hm
  simp only [knownFive, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact unitaryPerfect_six
  · exact unitaryPerfect_sixty
  · exact unitaryPerfect_ninety
  · exact unitaryPerfect_87360
  · exact unitaryPerfect_fifth

/-! ## A partial result: no odd number is unitary perfect -/

theorem two_pow_card_primeFactors_dvd_usigma {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) :
    2 ^ n.primeFactors.card ∣ usigma n := by
  rw [usigma_eq_factorization_prod hn, Finsupp.prod, Nat.support_factorization]
  rw [← Finset.prod_const]
  refine Finset.prod_dvd_prod_of_dvd _ _ ?_
  intro p hp
  have hpodd : Odd p := by
    rcases Nat.Prime.eq_two_or_odd' (Nat.prime_of_mem_primeFactors hp) with rfl | h
    · exact absurd (Nat.dvd_of_mem_primeFactors hp) (by
        simpa [Nat.two_dvd_ne_zero, Nat.odd_iff] using hodd)
    · exact h
  have : Odd (p ^ n.factorization p) := hpodd.pow
  rcases this with ⟨t, ht⟩
  exact ⟨t + 1, by omega⟩

theorem not_isUnitaryPerfect_of_odd {n : ℕ} (hodd : Odd n) : ¬ IsUnitaryPerfect n := by
  rintro ⟨hpos, heq⟩
  have hn : n ≠ 0 := hpos.ne'
  have hdvd := two_pow_card_primeFactors_dvd_usigma hn hodd
  rw [heq] at hdvd
  have hcard : n.primeFactors.card ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have h4 : (4 : ℕ) ∣ 2 * n := dvd_trans (by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ n.primeFactors.card := pow_dvd_pow 2 hlt) hdvd
    obtain ⟨c, hc⟩ := h4
    have : 2 ∣ n := ⟨c, by omega⟩
    rw [Nat.odd_iff] at hodd
    omega
  interval_cases h : n.primeFactors.card
  · -- no prime factors: n = 1
    have hn1 : n = 1 := by
      by_contra hne
      have : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
      rw [← Finset.card_pos, h] at this
      omega
    rw [hn1, usigma_one] at heq
    omega
  · -- exactly one prime factor: n is a prime power and σ*(n) = n + 1
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; exact Finset.mem_singleton_self p)
    have hnp : n = p ^ n.factorization p := by
      conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
      rw [Finsupp.prod, Nat.support_factorization, hp, Finset.prod_singleton]
    have husig : usigma n = p ^ n.factorization p + 1 := by
      rw [usigma_eq_factorization_prod hn, Finsupp.prod, Nat.support_factorization, hp,
        Finset.prod_singleton]
    have hpdvd : p ∣ n :=
      Nat.dvd_of_mem_primeFactors (by rw [hp]; exact Finset.mem_singleton_self p)
    have h2n : 2 ≤ n := hpp.two_le.trans (Nat.le_of_dvd hpos hpdvd)
    rw [husig, ← hnp] at heq
    omega

/-- Every unitary perfect number is even; in particular a sixth one, should it exist,
must be even. -/
theorem two_dvd_of_isUnitaryPerfect {n : ℕ} (hn : IsUnitaryPerfect n) : 2 ∣ n := by
  by_contra hodd
  exact not_isUnitaryPerfect_of_odd (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)) hn

/-! ## Main conditional statement -/

/-- **Conditional reduction (sixth unitary perfect number).**
Whether a sixth unitary perfect number exists is an open problem; only the five
numbers in `knownFive` are known.  This theorem gives the reduction: as soon as a
single unitary perfect number outside the known list exists, there are at least six
unitary perfect numbers, i.e. a sixth one exists.  The five known examples are
verified unconditionally in `knownFive_unitaryPerfect`. -/
theorem SixthUnitaryPerfectExists
    (h : ∃ n, IsUnitaryPerfect n ∧ n ∉ knownFive) :
    ∃ S : Finset ℕ, S.card = 6 ∧ ∀ m ∈ S, IsUnitaryPerfect m := by
  obtain ⟨n, hn, hnot⟩ := h
  refine ⟨insert n knownFive, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hnot, knownFive_card]
  · intro m hm
    rcases Finset.mem_insert.1 hm with rfl | hm
    · exact hn
    · exact knownFive_unitaryPerfect m hm

end Brockian.UnitaryPerfect

