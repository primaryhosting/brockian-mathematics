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

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => Nat.Coprime d (n / d)

/-- `usigma n` is `σ*(n)`, the sum of the unitary divisors of `n`. -/
def usigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is unitary perfect if it is positive and `σ*(n) = 2 n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ usigma n = 2 * n

lemma odd_of_dvd_odd {a b : ℕ} (h : a ∣ b) (hb : Odd b) : Odd a := by
  rcases Nat.even_or_odd a with he | ho
  · exfalso
    have h2 : (2 : ℕ) ∣ b := he.two_dvd.trans h
    rw [Nat.odd_iff] at hb
    omega
  · exact ho

/-- The five known unitary perfect numbers. -/
def knownUnitaryPerfect : Finset ℕ := {6, 60, 90, 87360, 146361946186458562560000}

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

@[simp] lemma usigma_one : usigma 1 = 1 := by decide

@[simp] lemma usigma_zero : usigma 0 = 0 := by decide

/-- `σ*` is multiplicative. -/
theorem usigma_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  -- the key computation: unitary divisors of `m * n` are products of unitary divisors
  have hdiv : ∀ {a b : ℕ}, a ∣ m → b ∣ n → m * n / (a * b) = m / a * (n / b) := by
    intro a b ha hb
    exact (Nat.div_mul_div_comm ha hb).symm
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun x _ => x.1 * x.2) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ha, -, ha2⟩, hb, -, hb2⟩ := hab
    have han : Nat.Coprime a (n / b) :=
      (Nat.Coprime.coprime_dvd_left ha h).coprime_dvd_right (Nat.div_dvd_of_dvd hb)
    have hbm : Nat.Coprime b (m / a) :=
      (Nat.Coprime.coprime_dvd_left hb h.symm).coprime_dvd_right (Nat.div_dvd_of_dvd ha)
    refine mem_unitaryDivisors.2 ⟨mul_dvd_mul ha hb, mul_ne_zero hm hn, ?_⟩
    rw [hdiv ha hb]
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right ha2 han) (Nat.Coprime.mul_right hbm hb2)
  · rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [Finset.mem_product, mem_unitaryDivisors] at h₁ h₂
    obtain ⟨⟨ha₁, -, -⟩, hb₁, -, -⟩ := h₁
    obtain ⟨⟨ha₂, -, -⟩, hb₂, -, -⟩ := h₂
    simp only at heq
    have hc12 : Nat.Coprime a₁ b₂ :=
      (Nat.Coprime.coprime_dvd_left ha₁ h).coprime_dvd_right hb₂
    have hc21 : Nat.Coprime a₂ b₁ :=
      (Nat.Coprime.coprime_dvd_left ha₂ h).coprime_dvd_right hb₁
    have hA : a₁ = a₂ := by
      have h1 : a₁ ∣ a₂ * b₂ := heq ▸ Dvd.intro b₁ rfl
      have h2 : a₂ ∣ a₁ * b₁ := heq ▸ Dvd.intro b₂ rfl
      exact Nat.dvd_antisymm (hc12.dvd_of_dvd_mul_right h1) (hc21.dvd_of_dvd_mul_right h2)
    have ha0 : a₁ ≠ 0 := by rintro rfl; exact hm (Nat.eq_zero_of_zero_dvd ha₁)
    subst hA
    have : b₁ = b₂ := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha0) heq
    simp [this]
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hdvd, -, hcop⟩ := hd
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
    rw [hdiv ha hb] at hcop
    have ha2 : Nat.Coprime a (m / a) :=
      (Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hcop).coprime_dvd_right
        (dvd_mul_right _ _)
    have hb2 : Nat.Coprime b (n / b) :=
      (Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hcop).coprime_dvd_right
        (dvd_mul_left _ _)
    exact ⟨(a, b), by
      simp only [Finset.mem_product, mem_unitaryDivisors]
      exact ⟨⟨ha, hm, ha2⟩, hb, hn, hb2⟩, rfl⟩
  · rintro ⟨a, b⟩ -
    rfl

lemma unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  ext d
  simp only [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hdvd, -, hcop⟩
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · left; simp
    · right
      have hdiv : p ^ k / p ^ j = p ^ (k - j) := by
        rw [Nat.pow_div hj hp.pos]
      rw [hdiv] at hcop
      have : k - j = 0 := by
        by_contra hne
        have hp1 : p ∣ p ^ j := dvd_pow_self p (by omega : j ≠ 0)
        have hp2 : p ∣ p ^ (k - j) := dvd_pow_self p hne
        have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hp1 hcop) hp2
        exact hp.one_lt.ne' this
      have : j = k := by omega
      rw [this]
  · rintro (rfl | rfl)
    · exact ⟨one_dvd _, pow_ne_zero _ hp.pos.ne', Nat.coprime_one_left _⟩
    · exact ⟨dvd_rfl, pow_ne_zero _ hp.pos.ne', by
        rw [Nat.div_self (Nat.pos_of_ne_zero (pow_ne_zero _ hp.pos.ne'))]
        exact Nat.coprime_one_right _⟩

lemma usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    usigma (p ^ k) = p ^ k + 1 := by
  have hne : (1 : ℕ) ≠ p ^ k := by
    have : 1 < p ^ k := Nat.one_lt_pow hk hp.one_lt
    omega
  rw [usigma, unitaryDivisors_prime_pow hp, Finset.sum_insert (by simpa using hne),
    Finset.sum_singleton]
  omega

/-- Any `n > 1` splits off a prime power unitary factor. -/
theorem usigma_split {n : ℕ} (hn : 1 < n) :
    ∃ q m : ℕ, 1 < q ∧ q * m = n ∧ Nat.Coprime q m ∧ usigma n = (q + 1) * usigma m := by
  have hn0 : n ≠ 0 := by omega
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ n := Nat.minFac_dvd n
  set k := n.factorization p
  have hk : k ≠ 0 := by
    have := (Nat.Prime.factorization_pos_of_dvd hp hn0 hpd)
    omega
  refine ⟨p ^ k, n / p ^ k, Nat.one_lt_pow hk hp.one_lt, Nat.ordProj_mul_ordCompl_eq_self n p, ?_, ?_⟩
  · exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
  · have hcop : Nat.Coprime (p ^ k) (n / p ^ k) :=
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
    have hm0 : n / p ^ k ≠ 0 := by
      intro h
      have := Nat.ordProj_mul_ordCompl_eq_self n p
      rw [h] at this
      omega
    calc usigma n = usigma (p ^ k * (n / p ^ k)) := by rw [Nat.ordProj_mul_ordCompl_eq_self n p]
      _ = usigma (p ^ k) * usigma (n / p ^ k) :=
          usigma_mul_of_coprime (pow_ne_zero _ hp.pos.ne') hm0 hcop
      _ = (p ^ k + 1) * usigma (n / p ^ k) := by rw [usigma_prime_pow hp hk]

lemma even_usigma_of_odd {n : ℕ} (hodd : Odd n) (hn : 1 < n) : Even (usigma n) := by
  obtain ⟨q, m, hq1, hqm, -, hus⟩ := usigma_split hn
  have hqodd : Odd q := odd_of_dvd_odd ⟨m, hqm.symm⟩ hodd
  rw [hus]
  exact (hqodd.add_one).mul_right _

/-- **Key lemma**: there is no odd unitary perfect number. -/
theorem not_isUnitaryPerfect_of_odd {n : ℕ} (hodd : Odd n) : ¬ IsUnitaryPerfect n := by
  rintro ⟨hpos, hperf⟩
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hpos.ne') with h1 | h1
  · rw [← h1] at hperf; simp at hperf
  obtain ⟨q, m, hq1, hqm, -, hus⟩ := usigma_split h1
  have hqodd : Odd q := odd_of_dvd_odd ⟨m, hqm.symm⟩ hodd
  have hmodd : Odd m := odd_of_dvd_odd (Dvd.intro_left q hqm) hodd
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 (by rintro rfl; omega : m ≠ 0)) with hm1 | hm1
  · -- `n` is a prime power
    rw [← hm1] at hqm hus
    simp only [mul_one, usigma_one] at hqm hus
    rw [hus, ← hqm] at hperf
    omega
  · -- `n` has at least two prime factors, so `4 ∣ σ*(n) = 2n`
    obtain ⟨t, ht⟩ := even_usigma_of_odd hmodd hm1
    obtain ⟨s, hs⟩ := hqodd
    have h4 : usigma n = 4 * ((s + 1) * t) := by
      rw [hus, ht, hs]; ring
    rw [h4] at hperf
    obtain ⟨r, hr⟩ := hodd
    omega

theorem isUnitaryPerfect_even {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exact absurd h (not_isUnitaryPerfect_of_odd ho)

lemma usigma_mul_prime_pow {m p k : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hk : k ≠ 0)
    (h : Nat.Coprime (p ^ k) m) : usigma (p ^ k * m) = (p ^ k + 1) * usigma m := by
  rw [usigma_mul_of_coprime (pow_ne_zero _ hp.pos.ne') hm h, usigma_prime_pow hp hk]

/-- One step of the computation of `σ*` from a prime factorization. -/
lemma usigma_step {N m p k s t : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hm : m ≠ 0)
    (hcop : Nat.Coprime (p ^ k) m) (hN : N = p ^ k * m) (hs : usigma m = s)
    (ht : t = (p ^ k + 1) * s) : usigma N = t := by
  subst hN; subst ht; subst hs
  exact usigma_mul_prime_pow hm hp hk hcop

theorem usigma_6 : usigma 6 = 12 := by
  have h0 : usigma 1 = 1 := usigma_one
  have h1 : usigma 3 = 4 :=
    usigma_step (p := 3) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h0 (by norm_num)
  have h2 : usigma 6 = 12 :=
    usigma_step (p := 2) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h1 (by norm_num)
  exact h2

theorem usigma_60 : usigma 60 = 120 := by
  have h0 : usigma 1 = 1 := usigma_one
  have h1 : usigma 5 = 6 :=
    usigma_step (p := 5) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h0 (by norm_num)
  have h2 : usigma 15 = 24 :=
    usigma_step (p := 3) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h1 (by norm_num)
  have h3 : usigma 60 = 120 :=
    usigma_step (p := 2) (k := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h2 (by norm_num)
  exact h3

theorem usigma_90 : usigma 90 = 180 := by
  have h0 : usigma 1 = 1 := usigma_one
  have h1 : usigma 5 = 6 :=
    usigma_step (p := 5) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h0 (by norm_num)
  have h2 : usigma 45 = 60 :=
    usigma_step (p := 3) (k := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h1 (by norm_num)
  have h3 : usigma 90 = 180 :=
    usigma_step (p := 2) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h2 (by norm_num)
  exact h3

theorem usigma_87360 : usigma 87360 = 174720 := by
  have h0 : usigma 1 = 1 := usigma_one
  have h1 : usigma 13 = 14 :=
    usigma_step (p := 13) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h0 (by norm_num)
  have h2 : usigma 91 = 112 :=
    usigma_step (p := 7) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h1 (by norm_num)
  have h3 : usigma 455 = 672 :=
    usigma_step (p := 5) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h2 (by norm_num)
  have h4 : usigma 1365 = 2688 :=
    usigma_step (p := 3) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h3 (by norm_num)
  have h5 : usigma 87360 = 174720 :=
    usigma_step (p := 2) (k := 6) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h4 (by norm_num)
  exact h5

theorem usigma_146361946186458562560000 : usigma 146361946186458562560000 = 292723892372917125120000 := by
  have h0 : usigma 1 = 1 := usigma_one
  have h1 : usigma 313 = 314 :=
    usigma_step (p := 313) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h0 (by norm_num)
  have h2 : usigma 49141 = 49612 :=
    usigma_step (p := 157) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h1 (by norm_num)
  have h3 : usigma 5356369 = 5457320 :=
    usigma_step (p := 109) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h2 (by norm_num)
  have h4 : usigma 423153151 = 436585600 :=
    usigma_step (p := 79) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h3 (by norm_num)
  have h5 : usigma 15656666587 = 16590252800 :=
    usigma_step (p := 37) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h4 (by norm_num)
  have h6 : usigma 297476665153 = 331805056000 :=
    usigma_step (p := 19) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h5 (by norm_num)
  have h7 : usigma 3867196646989 = 4645270784000 :=
    usigma_step (p := 13) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h6 (by norm_num)
  have h8 : usigma 42539163116879 = 55743249408000 :=
    usigma_step (p := 11) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h7 (by norm_num)
  have h9 : usigma 297774141818153 = 445945995264000 :=
    usigma_step (p := 7) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h8 (by norm_num)
  have h10 : usigma 186108838636345625 = 279162193035264000 :=
    usigma_step (p := 5) (k := 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h9 (by norm_num)
  have h11 : usigma 558326515909036875 = 1116648772141056000 :=
    usigma_step (p := 3) (k := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h10 (by norm_num)
  have h12 : usigma 146361946186458562560000 = 292723892372917125120000 :=
    usigma_step (p := 2) (k := 18) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h11 (by norm_num)
  exact h12

/-- The five known unitary perfect numbers really are unitary perfect. -/
theorem isUnitaryPerfect_of_mem_known {n : ℕ} (hn : n ∈ knownUnitaryPerfect) :
    IsUnitaryPerfect n := by
  fin_cases hn
  · exact ⟨by norm_num, by rw [usigma_6]⟩
  · exact ⟨by norm_num, by rw [usigma_60]⟩
  · exact ⟨by norm_num, by rw [usigma_90]⟩
  · exact ⟨by norm_num, by rw [usigma_87360]⟩
  · exact ⟨by norm_num, by rw [usigma_146361946186458562560000]⟩

/-- A unitary perfect number is not a prime power. -/
theorem not_isPrimePow_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) :
    ¬ IsPrimePow n := by
  rintro hpp
  obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff _ |>.1 hpp
  obtain ⟨-, hperf⟩ := h
  rw [usigma_prime_pow hp (by omega)] at hperf
  have h1 : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  omega

/-- The (open) statement that a sixth unitary perfect number exists. -/
def SixthUnitaryPerfectExistsStatement : Prop :=
  ∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect

/-- **Conditional reduction for the sixth unitary perfect number.**
The existence of a unitary perfect number besides the five known ones is equivalent to the
existence of such a number that is moreover even and not a prime power.  In other words, the
search for a sixth unitary perfect number may be restricted to even numbers with at least two
distinct prime factors.  (Whether a sixth unitary perfect number exists is an open problem, so
the statement itself is not proved here; what is proved is this reduction.) -/
theorem SixthUnitaryPerfectExists :
    SixthUnitaryPerfectExistsStatement ↔
      ∃ n, IsUnitaryPerfect n ∧ Even n ∧ ¬ IsPrimePow n ∧ n ∉ knownUnitaryPerfect := by
  constructor
  · rintro ⟨n, hn, hnot⟩
    exact ⟨n, hn, isUnitaryPerfect_even hn, not_isPrimePow_of_isUnitaryPerfect hn, hnot⟩
  · rintro ⟨n, hn, -, -, hnot⟩
    exact ⟨n, hn, hnot⟩

end Brockian.UnitaryPerfect

