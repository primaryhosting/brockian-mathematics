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

set_option maxRecDepth 8000

open Finset

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d` of `n` with `d` coprime to `n / d`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- The unitary divisor sum `σ*(n) = ∑_{d ‖ n} d`. -/
def usigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is *unitary perfect* if it is positive and `σ*(n) = 2n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ usigma n = 2 * n

/-- The five unitary perfect numbers known in the literature. -/
def knownUnitaryPerfect : Finset ℕ := {6, 60, 90, 87360, 146361946186458562560000}

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ (d ∣ n ∧ n ≠ 0) ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

/-! ## Multiplicativity of `σ*` -/

/-- `σ*` is multiplicative: for coprime positive `m`, `n` we have `σ*(mn) = σ*(m)σ*(n)`. -/
theorem usigma_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  refine (Finset.sum_bij (fun x _ => x.1 * x.2) ?_ ?_ ?_ ?_).symm
  · -- the product of a unitary divisor of `m` and one of `n` is a unitary divisor of `m * n`
    rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨⟨ha, -⟩, hca⟩, ⟨hb, -⟩, hcb⟩ := hab
    refine mem_unitaryDivisors.2 ⟨⟨mul_dvd_mul ha hb, hmn⟩, ?_⟩
    rw [← Nat.div_mul_div_comm ha hb]
    have han : Nat.Coprime a (n / b) :=
      (h.coprime_dvd_left ha).coprime_dvd_right (Nat.div_dvd_of_dvd hb)
    have hbm : Nat.Coprime b (m / a) :=
      (h.symm.coprime_dvd_left hb).coprime_dvd_right (Nat.div_dvd_of_dvd ha)
    exact Nat.Coprime.mul_left (hca.mul_right han) (hbm.mul_right hcb)
  · -- injectivity
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab hab'
    obtain ⟨⟨⟨ha, -⟩, -⟩, ⟨hb, -⟩, -⟩ := hab
    obtain ⟨⟨⟨ha', -⟩, -⟩, ⟨hb', -⟩, -⟩ := hab'
    simp only at heq
    have hab1 : Nat.Coprime a b' := (h.coprime_dvd_left ha).coprime_dvd_right hb'
    have hab2 : Nat.Coprime a' b := (h.coprime_dvd_left ha').coprime_dvd_right hb
    have h1 : a ∣ a' := hab1.dvd_of_dvd_mul_right (heq ▸ Dvd.intro b rfl)
    have h2 : a' ∣ a := hab2.dvd_of_dvd_mul_right (heq ▸ Dvd.intro b' rfl)
    have haa : a = a' := Nat.dvd_antisymm h1 h2
    subst haa
    have hapos : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact hm (Nat.eq_zero_of_zero_dvd ha))
    have : b = b' := Nat.eq_of_mul_eq_mul_left hapos heq
    simp [this]
  · -- surjectivity
    intro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨⟨hdvd, -⟩, hcop⟩ := hd
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
    rw [← Nat.div_mul_div_comm ha hb] at hcop
    refine ⟨(a, b), ?_, rfl⟩
    simp only [Finset.mem_product, mem_unitaryDivisors]
    refine ⟨⟨⟨ha, hm⟩, ?_⟩, ⟨hb, hn⟩, ?_⟩
    · exact (hcop.coprime_dvd_left (Dvd.intro b rfl)).coprime_dvd_right (Dvd.intro (n / b) rfl)
    · exact (hcop.coprime_dvd_left (Dvd.intro_left a rfl)).coprime_dvd_right
        (Dvd.intro_left (m / a) rfl)
  · rintro ⟨a, b⟩ hab
    rfl

/-- The unitary divisors of a prime power `p ^ k` are exactly `1` and `p ^ k`. -/
theorem unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
  ext d
  simp only [mem_unitaryDivisors, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨hd, -⟩, hcop⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · left; simp
    · right
      rw [Nat.pow_div hi hp.pos] at hcop
      have hik : k - i = 0 := by
        by_contra hne
        have hdvd : p ∣ Nat.gcd (p ^ i) (p ^ (k - i)) :=
          Nat.dvd_gcd (dvd_pow_self p hipos.ne') (dvd_pow_self p hne)
        rw [Nat.Coprime] at hcop
        rw [hcop] at hdvd
        exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd)
      have : i = k := by omega
      rw [this]
  · rintro (rfl | rfl)
    · exact ⟨⟨one_dvd _, hpk⟩, Nat.coprime_one_left _⟩
    · exact ⟨⟨dvd_rfl, hpk⟩, by simp [Nat.div_self (Nat.pos_of_ne_zero hpk)]⟩

/-- `σ*(p ^ k) = p ^ k + 1` for a prime `p` and `k ≥ 1`. -/
theorem usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    usigma (p ^ k) = p ^ k + 1 := by
  rw [usigma, unitaryDivisors_prime_pow hp]
  have h1 : (1 : ℕ) ≠ p ^ k := (Nat.one_lt_pow hk hp.one_lt).ne
  rw [Finset.sum_insert (by simpa using h1)]
  simp [add_comm]

/-- `σ*(p) = p + 1` for a prime `p`. -/
theorem usigma_prime {p : ℕ} (hp : p.Prime) : usigma p = p + 1 := by
  simpa using usigma_prime_pow (k := 1) hp one_ne_zero

/-- Peeling off a coprime prime power factor. -/
theorem usigma_mul_prime_pow {m p k : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hk : k ≠ 0)
    (hcop : Nat.Coprime m (p ^ k)) : usigma (m * p ^ k) = usigma m * (p ^ k + 1) := by
  rw [usigma_mul_of_coprime hm (pow_ne_zero _ hp.pos.ne') hcop, usigma_prime_pow hp hk]

/-- Peeling off a coprime prime factor. -/
theorem usigma_mul_prime {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    usigma (m * p) = usigma m * (p + 1) := by
  rw [usigma_mul_of_coprime hm hp.pos.ne' hcop, usigma_prime hp]

/-! ## The five known unitary perfect numbers -/

theorem usigma_six : usigma 6 = 12 := by
  have e1 : usigma 2 = 3 := usigma_prime (by norm_num)
  have e2 : usigma (2 * 3) = usigma 2 * (3 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  norm_num [e1] at e2
  norm_num [e2]

theorem usigma_sixty : usigma 60 = 120 := by
  have e1 : usigma 4 = 5 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, usigma_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have e2 : usigma (2 ^ 2 * 3) = usigma (2 ^ 2) * (3 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e3 : usigma (2 ^ 2 * 3 * 5) = usigma (2 ^ 2 * 3) * (5 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  norm_num [e1] at e2
  norm_num [e2] at e3
  exact e3

theorem usigma_ninety : usigma 90 = 180 := by
  have e1 : usigma 2 = 3 := usigma_prime (by norm_num)
  have e2 : usigma (2 * 3 ^ 2) = usigma 2 * (3 ^ 2 + 1) :=
    usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e3 : usigma (2 * 3 ^ 2 * 5) = usigma (2 * 3 ^ 2) * (5 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  norm_num [e1] at e2
  norm_num [e2] at e3
  exact e3

theorem usigma_87360 : usigma 87360 = 174720 := by
  have e1 : usigma 64 = 65 := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, usigma_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have e2 : usigma (2 ^ 6 * 3) = usigma (2 ^ 6) * (3 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e3 : usigma (2 ^ 6 * 3 * 5) = usigma (2 ^ 6 * 3) * (5 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e4 : usigma (2 ^ 6 * 3 * 5 * 7) = usigma (2 ^ 6 * 3 * 5) * (7 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e5 : usigma (2 ^ 6 * 3 * 5 * 7 * 13) = usigma (2 ^ 6 * 3 * 5 * 7) * (13 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  norm_num [e1] at e2
  norm_num [e2] at e3
  norm_num [e3] at e4
  norm_num [e4] at e5
  exact e5

theorem usigma_fifth : usigma 146361946186458562560000 = 292723892372917125120000 := by
  have e1 : usigma 262144 = 262145 := by
    rw [show (262144 : ℕ) = 2 ^ 18 by norm_num, usigma_prime_pow (by norm_num) (by norm_num)]
    norm_num
  have e2 : usigma (2 ^ 18 * 3) = usigma (2 ^ 18) * (3 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e3 : usigma (2 ^ 18 * 3 * 5 ^ 4) = usigma (2 ^ 18 * 3) * (5 ^ 4 + 1) :=
    usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e4 : usigma (2 ^ 18 * 3 * 5 ^ 4 * 7) = usigma (2 ^ 18 * 3 * 5 ^ 4) * (7 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e5 : usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11) = usigma (2 ^ 18 * 3 * 5 ^ 4 * 7) * (11 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e6 : usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13)
      = usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11) * (13 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e7 : usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19)
      = usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13) * (19 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e8 : usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37)
      = usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19) * (37 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e9 : usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37 * 79)
      = usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37) * (79 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e10 : usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37 * 79 * 109)
      = usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37 * 79) * (109 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e11 : usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157)
      = usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37 * 79 * 109) * (157 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  have e12 : usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313)
      = usigma (2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157) * (313 + 1) :=
    usigma_mul_prime (by norm_num) (by norm_num) (by norm_num [Nat.Coprime])
  norm_num [e1] at e2
  norm_num [e2] at e3
  norm_num [e3] at e4
  norm_num [e4] at e5
  norm_num [e5] at e6
  norm_num [e6] at e7
  norm_num [e7] at e8
  norm_num [e8] at e9
  norm_num [e9] at e10
  norm_num [e10] at e11
  norm_num [e11] at e12
  exact e12

theorem isUnitaryPerfect_six : IsUnitaryPerfect 6 := ⟨by norm_num, by norm_num [usigma_six]⟩

theorem isUnitaryPerfect_sixty : IsUnitaryPerfect 60 := ⟨by norm_num, by norm_num [usigma_sixty]⟩

theorem isUnitaryPerfect_ninety : IsUnitaryPerfect 90 := ⟨by norm_num, by norm_num [usigma_ninety]⟩

theorem isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 :=
  ⟨by norm_num, by norm_num [usigma_87360]⟩

theorem isUnitaryPerfect_fifth : IsUnitaryPerfect 146361946186458562560000 :=
  ⟨by norm_num, by norm_num [usigma_fifth]⟩

/-- All five numbers of `knownUnitaryPerfect` really are unitary perfect. -/
theorem knownUnitaryPerfect_isUnitaryPerfect :
    ∀ n ∈ knownUnitaryPerfect, IsUnitaryPerfect n := by
  intro n hn
  simp only [knownUnitaryPerfect, mem_insert, mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact isUnitaryPerfect_six
  · exact isUnitaryPerfect_sixty
  · exact isUnitaryPerfect_ninety
  · exact isUnitaryPerfect_87360
  · exact isUnitaryPerfect_fifth

/-! ## Every unitary perfect number is even -/

theorem usigma_one : usigma 1 = 1 := by decide

theorem usigma_mul_of_coprime' (x y : ℕ) (h : Nat.Coprime x y) :
    usigma (x * y) = usigma x * usigma y := by
  rcases eq_or_ne x 0 with rfl | hx
  · obtain rfl : y = 1 := (Nat.coprime_zero_left y).1 h
    simp [usigma_one]
  rcases eq_or_ne y 0 with rfl | hy
  · obtain rfl : x = 1 := (Nat.coprime_zero_right x).1 h
    simp [usigma_one]
  exact usigma_mul_of_coprime hx hy h

/-- `σ*(n)` is the product of `p ^ k + 1` over the prime powers `p ^ k` exactly dividing `n`. -/
theorem usigma_eq_prod_primeFactors {n : ℕ} (hn : n ≠ 0) :
    usigma n = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
  rw [Nat.multiplicative_factorization usigma usigma_mul_of_coprime' usigma_one hn,
    Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hk : n.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hp
  exact usigma_prime_pow (Nat.prime_of_mem_primeFactors hp) hk

/-- There is no odd unitary perfect number: every unitary perfect number is even. -/
theorem even_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  obtain ⟨hpos, hsum⟩ := h
  by_contra hne
  have hodd : Odd n := Nat.not_even_iff_odd.1 hne
  have hn0 : n ≠ 0 := hpos.ne'
  have hprod := usigma_eq_prod_primeFactors hn0
  have hdvd : 2 ^ #n.primeFactors ∣ usigma n := by
    rw [hprod, ← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.2 (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))) hodd
    have hppow : Odd (p ^ n.factorization p) := (hpp.odd_of_ne_two hp2).pow
    exact (Nat.even_add_one.2 (Nat.not_even_iff_odd.2 hppow)).two_dvd
  rw [hsum] at hdvd
  have hcard : #n.primeFactors ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h4 : (2 : ℕ) ^ 2 ∣ 2 ^ #n.primeFactors := pow_dvd_pow 2 hc
    obtain ⟨c, hc'⟩ := h4.trans hdvd
    exact (Nat.not_odd_iff_even.2 ⟨c, by omega⟩) hodd
  have hn1 : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.factorization_prod_pow_eq_self hn0
  rcases Nat.eq_zero_or_pos #n.primeFactors with h0 | h1
  · rw [Finset.card_eq_zero.1 h0, Finset.prod_empty] at hn1
    rw [← hn1, usigma_one] at hsum
    omega
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 (le_antisymm hcard h1)
    rw [hp, Finset.prod_singleton] at hprod hn1
    rw [hn1, hsum] at hprod
    have hn : n = 1 := by omega
    rw [hn] at hp
    simp at hp

/-! ## A sixth unitary perfect number -/

/-- **Conditional reduction.** Whether a sixth unitary perfect number exists is open. If some
unitary perfect number exceeds the largest known one, then there is a unitary perfect number
outside the five known ones, i.e. a sixth unitary perfect number. -/
theorem SixthUnitaryPerfectExists
    (h : ∃ n, IsUnitaryPerfect n ∧ 146361946186458562560000 < n) :
    ∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect := by
  obtain ⟨n, hn, hlt⟩ := h
  refine ⟨n, hn, ?_⟩
  simp only [knownUnitaryPerfect, mem_insert, mem_singleton]
  push_neg
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- If there are infinitely many unitary perfect numbers, then a sixth one exists. -/
theorem sixth_of_infinite (h : {n : ℕ | IsUnitaryPerfect n}.Infinite) :
    ∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect := by
  obtain ⟨n, hn, hn2⟩ := (h.diff knownUnitaryPerfect.finite_toSet).nonempty
  exact ⟨n, hn, hn2⟩

end Brockian.UnitaryPerfect

