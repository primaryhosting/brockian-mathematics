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
/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists

(The header block above is repeated here as a module docstring: Lean requires `import`
commands to precede any doc comment, so the file-opening header is an ordinary comment.)

Unitary divisors, the unitary divisor sum `σ*`, unitary perfect numbers, verification of the
five known unitary perfect numbers, the fact that no odd number `> 1` is unitary perfect, and
a reduction of the open "sixth unitary perfect number" problem.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd (d, n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- `sigmaStar n = σ*(n)` is the sum of the unitary divisors of `n`. -/
def sigmaStar (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is *unitary perfect* if it is positive and `σ*(n) = 2 n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ sigmaStar n = 2 * n

/-- The five known unitary perfect numbers. -/
def knownUnitaryPerfect : Finset ℕ :=
  {6, 60, 90, 87360, 146361946186458562560000}

lemma mem_unitaryDivisors {d n : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ Nat.Coprime d (n / d) ∧ n ≠ 0 := by
  simp [unitaryDivisors, Nat.mem_divisors]
  tauto

/-! ## Multiplicativity of `σ*` -/

/-- `σ*` is multiplicative: this is the key intermediate lemma. -/
theorem sigmaStar_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    sigmaStar (m * n) = sigmaStar m * sigmaStar n := by
  rw [sigmaStar, sigmaStar, sigmaStar, Finset.sum_mul_sum, ← Finset.sum_product']
  refine (Finset.sum_nbij' (i := fun p : ℕ × ℕ => p.1 * p.2)
    (j := fun d => (Nat.gcd d m, Nat.gcd d n)) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, mem_unitaryDivisors] at hp
    obtain ⟨⟨ha, hax, -⟩, ⟨hb, hby, -⟩⟩ := hp
    refine mem_unitaryDivisors.2 ⟨mul_dvd_mul ha hb, ?_, by positivity⟩
    have hdiv : m * n / (a * b) = (m / a) * (n / b) := (Nat.div_mul_div_comm ha hb).symm
    rw [hdiv]
    have h1 : Nat.Coprime a (n / b) :=
      (h.coprime_dvd_left ha).coprime_dvd_right (Nat.div_dvd_of_dvd hb)
    have h2 : Nat.Coprime b (m / a) :=
      ((h.symm).coprime_dvd_left hb).coprime_dvd_right (Nat.div_dvd_of_dvd ha)
    exact Nat.Coprime.mul_left (hax.mul_right h1) (h2.mul_right hby)
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hdvd, hcop, -⟩ := hd
    have hkey : Nat.gcd d m * Nat.gcd d n = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hdvd
    have h1 : Nat.gcd d m ∣ m := Nat.gcd_dvd_right d m
    have h2 : Nat.gcd d n ∣ n := Nat.gcd_dvd_right d n
    have hd1 : Nat.gcd d m ∣ d := Dvd.intro _ hkey
    have hd2 : Nat.gcd d n ∣ d := Dvd.intro_left _ hkey
    have hdiv : m * n / d = (m / Nat.gcd d m) * (n / Nat.gcd d n) := by
      rw [Nat.div_mul_div_comm h1 h2, hkey]
    simp only [Finset.mem_product, mem_unitaryDivisors]
    refine ⟨⟨h1, ?_, hm.ne'⟩, ⟨h2, ?_, hn.ne'⟩⟩
    · refine (hcop.coprime_dvd_left hd1).coprime_dvd_right ?_
      rw [hdiv]; exact Dvd.intro _ rfl
    · refine (hcop.coprime_dvd_left hd2).coprime_dvd_right ?_
      rw [hdiv]; exact Dvd.intro_left _ rfl
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, mem_unitaryDivisors] at hp
    obtain ⟨⟨ha, -, -⟩, ⟨hb, -, -⟩⟩ := hp
    have hbm : Nat.Coprime b m := (h.symm).coprime_dvd_left hb
    have ham : Nat.Coprime a n := h.coprime_dvd_left ha
    have e1 : Nat.gcd (a * b) m = a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a hbm, Nat.gcd_eq_left ha]
    have e2 : Nat.gcd (a * b) n = b := by
      rw [Nat.Coprime.gcd_mul_left_cancel b ham, Nat.gcd_eq_left hb]
    simp [e1, e2]
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hd.1
  · intro p _; rfl

theorem unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  ext d
  rw [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hdvd, hcop, -⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rw [Nat.pow_div hi hp.pos] at hcop
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · have hki : k - i = 0 := by
        by_contra hne
        have hpi : p ∣ p ^ i := dvd_pow_self p hi0.ne'
        have hpk' : p ∣ p ^ (k - i) := dvd_pow_self p hne
        exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpi hpk')
      right
      have : i = k := by omega
      simp [this]
  · rintro (rfl | rfl)
    · exact ⟨one_dvd _, by simp, hpk.ne'⟩
    · exact ⟨dvd_rfl, by simp [Nat.div_self hpk], hpk.ne'⟩

theorem sigmaStar_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    sigmaStar (p ^ k) = p ^ k + 1 := by
  have h1 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
  rw [sigmaStar, unitaryDivisors_prime_pow hp,
    Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  omega

theorem sigmaStar_one : sigmaStar 1 = 1 := by decide

/-- Splitting off a prime power factor. -/
theorem sigmaStar_prime_pow_mul {p k m : ℕ} (hp : p.Prime) (hk : 0 < k) (hm : 0 < m)
    (h : Nat.Coprime (p ^ k) m) : sigmaStar (p ^ k * m) = (p ^ k + 1) * sigmaStar m := by
  rw [sigmaStar_mul_of_coprime (pow_pos hp.pos k) hm h, sigmaStar_prime_pow hp hk]

/-! ## The five known unitary perfect numbers -/

theorem unitaryPerfect_six : IsUnitaryPerfect 6 := by
  refine ⟨by norm_num, ?_⟩
  have e : (6 : ℕ) = 2 ^ 1 * 3 ^ 1 := by norm_num
  rw [e, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow (p := 3) (k := 1) (by norm_num) (by norm_num)]
  norm_num

theorem unitaryPerfect_sixty : IsUnitaryPerfect 60 := by
  refine ⟨by norm_num, ?_⟩
  have e : (60 : ℕ) = 2 ^ 2 * (3 ^ 1 * 5 ^ 1) := by norm_num
  rw [e, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow (p := 5) (k := 1) (by norm_num) (by norm_num)]
  norm_num

theorem unitaryPerfect_ninety : IsUnitaryPerfect 90 := by
  refine ⟨by norm_num, ?_⟩
  have e : (90 : ℕ) = 2 ^ 1 * (3 ^ 2 * 5 ^ 1) := by norm_num
  rw [e, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow (p := 5) (k := 1) (by norm_num) (by norm_num)]
  norm_num

theorem unitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  refine ⟨by norm_num, ?_⟩
  have e : (87360 : ℕ) = 2 ^ 6 * (3 ^ 1 * (5 ^ 1 * (7 ^ 1 * 13 ^ 1))) := by norm_num
  rw [e, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow (p := 13) (k := 1) (by norm_num) (by norm_num)]
  norm_num

theorem unitaryPerfect_huge : IsUnitaryPerfect 146361946186458562560000 := by
  refine ⟨by norm_num, ?_⟩
  have e : (146361946186458562560000 : ℕ) =
      2 ^ 18 * (3 ^ 1 * (5 ^ 4 * (7 ^ 1 * (11 ^ 1 * (13 ^ 1 * (19 ^ 1 * (37 ^ 1 *
        (79 ^ 1 * (109 ^ 1 * (157 ^ 1 * 313 ^ 1)))))))))) := by norm_num
  rw [e, sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow_mul (by norm_num) (by norm_num) (by norm_num) (by decide),
    sigmaStar_prime_pow (p := 313) (k := 1) (by norm_num) (by norm_num)]
  norm_num

theorem knownUnitaryPerfect_unitaryPerfect {n : ℕ} (hn : n ∈ knownUnitaryPerfect) :
    IsUnitaryPerfect n := by
  simp only [knownUnitaryPerfect, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact unitaryPerfect_six
  · exact unitaryPerfect_sixty
  · exact unitaryPerfect_ninety
  · exact unitaryPerfect_87360
  · exact unitaryPerfect_huge

/-! ## No odd unitary perfect number exceeds `1` -/

/-- For odd `m > 1`, `σ*(m)` is even. -/
theorem even_sigmaStar_of_odd {m : ℕ} (hodd : Odd m) (h1 : 1 < m) : Even (sigmaStar m) := by
  set p := m.minFac with hpdef
  have hm0 : m ≠ 0 := by omega
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ m := Nat.minFac_dvd m
  have hk : 0 < m.factorization p := hp.factorization_pos_of_dvd hm0 hpdvd
  have hsplit : p ^ m.factorization p * (m / p ^ m.factorization p) = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  have hcop : Nat.Coprime (p ^ m.factorization p) (m / p ^ m.factorization p) :=
    (Nat.coprime_ordCompl hp hm0).pow_left _
  have hpos : 0 < m / p ^ m.factorization p := Nat.ordCompl_pos p hm0
  have hs : sigmaStar m = (p ^ m.factorization p + 1) * sigmaStar (m / p ^ m.factorization p) := by
    conv_lhs => rw [← hsplit]
    exact sigmaStar_prime_pow_mul hp hk hpos hcop
  have hpodd : Odd p := hodd.of_dvd_nat hpdvd
  have : Odd (p ^ m.factorization p) := hpodd.pow
  rw [hs]
  exact (Odd.add_one this).mul_right _

theorem not_unitaryPerfect_of_odd {n : ℕ} (hodd : Odd n) (h1 : 1 < n) :
    ¬ IsUnitaryPerfect n := by
  rintro ⟨-, hperf⟩
  set p := n.minFac with hpdef
  have hn0 : n ≠ 0 := by omega
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ n := Nat.minFac_dvd n
  have hk : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0 hpdvd
  set k := n.factorization p with hkdef
  set m := n / p ^ k with hmdef
  have hsplit : p ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : Nat.Coprime (p ^ k) m := (Nat.coprime_ordCompl hp hn0).pow_left _
  have hpos : 0 < m := Nat.ordCompl_pos p hn0
  have hs : sigmaStar n = (p ^ k + 1) * sigmaStar m := by
    conv_lhs => rw [← hsplit]
    exact sigmaStar_prime_pow_mul hp hk hpos hcop
  have hpodd : Odd p := hodd.of_dvd_nat hpdvd
  have hppow : Odd (p ^ k) := hpodd.pow
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hpos.ne') with h | hm1
  · -- `m = 1`, so `n = p ^ k` and `p ^ k + 1 = 2 p ^ k` forces `p ^ k = 1`
    have hm : m = 1 := h.symm
    have hnp : n = p ^ k := by rw [← hsplit, hm, mul_one]
    rw [hs, hm, sigmaStar_one, mul_one, hnp] at hperf
    have : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
    omega
  · -- `m > 1` is odd, so `σ*(m)` is even and `4 ∣ σ*(n) = 2 n`, contradicting `n` odd
    have hmodd : Odd m := hodd.of_dvd_nat ⟨p ^ k, by rw [← hsplit]; ring⟩
    obtain ⟨c, hc⟩ := even_sigmaStar_of_odd hmodd hm1
    obtain ⟨t, ht⟩ := hppow
    obtain ⟨u, hu⟩ := hodd
    have hexp : (p ^ k + 1) * sigmaStar m = 4 * ((t + 1) * c) := by rw [hc, ht]; ring
    rw [hs, hexp, hu] at hperf
    omega

theorem even_of_unitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) (h1 : 1 < n) : Even n := by
  rcases Nat.even_or_odd n with he | ho
  · exact he
  · exact absurd h (not_unitaryPerfect_of_odd ho h1)

/-! ## Unitary perfect numbers with at most two distinct prime factors -/

/-- An even number `2 ^ a * m` (with `m` odd) is unitary perfect exactly when
`(2 ^ a + 1) σ*(m) = 2 ^ (a+1) m`. -/
theorem unitaryPerfect_two_pow_mul_iff {a m : ℕ} (ha : 1 ≤ a) (hm : Odd m) (hm0 : 0 < m) :
    IsUnitaryPerfect (2 ^ a * m) ↔ (2 ^ a + 1) * sigmaStar m = 2 ^ (a + 1) * m := by
  have hcop : Nat.Coprime (2 ^ a) m := (Nat.coprime_two_left.mpr hm).pow_left _
  have hs : sigmaStar (2 ^ a * m) = (2 ^ a + 1) * sigmaStar m :=
    sigmaStar_prime_pow_mul Nat.prime_two (by omega) hm0 hcop
  constructor
  · rintro ⟨-, hperf⟩
    rw [hs] at hperf
    rw [hperf, pow_succ]
    ring
  · intro hrel
    refine ⟨by positivity, ?_⟩
    rw [hs, hrel, pow_succ]
    ring

/-- If `2 ^ a * p ^ k` (with `a, k ≥ 1`, `p` an odd prime) is unitary perfect, then it is `6`. -/
theorem eq_six_of_unitaryPerfect_two_pow_mul_prime_pow {a p k : ℕ} (ha : 1 ≤ a) (hp : p.Prime)
    (hpodd : Odd p) (hk : 1 ≤ k) (h : IsUnitaryPerfect (2 ^ a * p ^ k)) : 2 ^ a * p ^ k = 6 := by
  have hPodd : Odd (p ^ k) := hpodd.pow
  have hPpos : 0 < p ^ k := pow_pos hp.pos k
  have hrel := (unitaryPerfect_two_pow_mul_iff ha hPodd hPpos).1 h
  rw [sigmaStar_prime_pow hp hk] at hrel
  have hA2 : 2 ≤ 2 ^ a := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hne : p ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hpodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hP3 : 3 ≤ p ^ k := by
    calc (3 : ℕ) ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
  have hkey : 2 ^ a + p ^ k + 1 = 2 ^ a * p ^ k := by
    have e1 : (2 ^ a + 1) * (p ^ k + 1) = 2 ^ a * p ^ k + (2 ^ a + p ^ k + 1) := by ring
    have e2 : 2 ^ (a + 1) * p ^ k = 2 ^ a * p ^ k + 2 ^ a * p ^ k := by rw [pow_succ]; ring
    rw [e1, e2] at hrel
    exact Nat.add_left_cancel hrel
  have hfin : 2 ^ a = 2 ∧ p ^ k = 3 := by
    constructor <;> nlinarith [hkey, hA2, hP3]
  rw [hfin.1, hfin.2]

theorem card_primeFactors_two_pow_mul {a m : ℕ} (ha : 1 ≤ a) (hm : Odd m) (hm0 : 0 < m) :
    (2 ^ a * m).primeFactors.card = 1 + m.primeFactors.card := by
  have h2 : (2 ^ a).primeFactors = {2} := by
    rw [Nat.primeFactors_pow _ (by omega), Nat.Prime.primeFactors Nat.prime_two]
  have hdisj : Disjoint ({2} : Finset ℕ) m.primeFactors := by
    simp only [Finset.disjoint_singleton_left, Nat.mem_primeFactors, not_and]
    intro _ hc
    rcases hm with ⟨t, ht⟩
    omega
  rw [Nat.primeFactors_mul (by positivity) hm0.ne', h2, Finset.card_union_of_disjoint hdisj]
  simp

/-- Every unitary perfect number other than `6` has at least three distinct prime factors.
In particular a sixth unitary perfect number, if one exists, has at least three distinct
prime factors. -/
theorem three_le_card_primeFactors_of_unitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n)
    (hn6 : n ≠ 6) : 3 ≤ n.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hn0 : n ≠ 0 := h.1.ne'
  have hn1 : 1 < n := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · omega
      · have h1 := h.2
        rw [sigmaStar_one] at h1
        omega
    · omega
  set a := n.factorization 2 with hadef
  set m := n / 2 ^ a with hmdef
  have hsplit : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have ha : 1 ≤ a :=
    Nat.prime_two.factorization_pos_of_dvd hn0 (even_of_unitaryPerfect h hn1).two_dvd
  have hm0 : 0 < m := Nat.ordCompl_pos 2 hn0
  have hmodd : Odd m := by
    have h2 : ¬ (2 ∣ m) := Nat.not_dvd_ordCompl Nat.prime_two hn0
    exact Nat.odd_iff.2 (by omega)
  have hA2 : 2 ≤ 2 ^ a := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hcard : n.primeFactors.card = 1 + m.primeFactors.card := by
    conv_lhs => rw [← hsplit]
    exact card_primeFactors_two_pow_mul ha hmodd hm0
  have hmcard : m.primeFactors.card ≤ 1 := by omega
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hm0.ne') with hm1 | hm1
  · -- `m = 1`, i.e. `n = 2 ^ a`, which is never unitary perfect
    have hnp : n = 2 ^ a := by rw [← hsplit, ← hm1, mul_one]
    have h2 := h.2
    rw [hnp, sigmaStar_prime_pow Nat.prime_two (by omega)] at h2
    omega
  · -- `m > 1` has exactly one prime factor, so `n = 2 ^ a * q ^ j` and hence `n = 6`
    have hpos : 0 < m.primeFactors.card :=
      Finset.card_pos.2 (Nat.nonempty_primeFactors.2 hm1)
    have hpp : IsPrimePow m := isPrimePow_iff_card_primeFactors_eq_one.2 (by omega)
    obtain ⟨q, j, hq, hj, hqm⟩ := hpp
    have hq' : q.Prime := Nat.prime_iff.2 hq
    have hqodd : Odd q := hmodd.of_dvd_nat (hqm ▸ dvd_pow_self q hj.ne')
    have hup : IsUnitaryPerfect (2 ^ a * q ^ j) := by rw [hqm, hsplit]; exact h
    have := eq_six_of_unitaryPerfect_two_pow_mul_prime_pow ha hq' hqodd hj hup
    rw [hqm, hsplit] at this
    exact hn6 this

/-! ## Reduction of the sixth-unitary-perfect problem -/

/-- **Reduction theorem.** A sixth unitary perfect number exists if and only if there are
`a ≥ 1` and an odd `m ≥ 1` with `(2 ^ a + 1) σ*(m) = 2 ^ (a+1) m` such that `2 ^ a * m` is
not one of the five known unitary perfect numbers. -/
theorem sixth_exists_iff :
    (∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect) ↔
      (∃ a m : ℕ, 1 ≤ a ∧ Odd m ∧ 0 < m ∧
        (2 ^ a + 1) * sigmaStar m = 2 ^ (a + 1) * m ∧ 2 ^ a * m ∉ knownUnitaryPerfect) := by
  constructor
  · rintro ⟨n, hn, hnot⟩
    have hn0 : n ≠ 0 := hn.1.ne'
    have hn1 : 1 < n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n
        · omega
        · exfalso
          have := hn.2
          rw [sigmaStar_one] at this
          omega
      · omega
    set a := n.factorization 2 with hadef
    set m := n / 2 ^ a with hmdef
    have hsplit : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
    have ha : 1 ≤ a :=
      Nat.prime_two.factorization_pos_of_dvd hn0 (even_of_unitaryPerfect hn hn1).two_dvd
    have hm0 : 0 < m := Nat.ordCompl_pos 2 hn0
    have hmodd : Odd m := by
      have h2 : ¬ (2 ∣ m) := Nat.not_dvd_ordCompl Nat.prime_two hn0
      exact Nat.odd_iff.2 (by omega)
    refine ⟨a, m, ha, hmodd, hm0, ?_, ?_⟩
    · exact (unitaryPerfect_two_pow_mul_iff ha hmodd hm0).1 (by rwa [hsplit])
    · rwa [hsplit]
  · rintro ⟨a, m, ha, hmodd, hm0, hrel, hnot⟩
    exact ⟨2 ^ a * m, (unitaryPerfect_two_pow_mul_iff ha hmodd hm0).2 hrel, hnot⟩

/-- **Sixth unitary perfect number (conditional).**

Whether a sixth unitary perfect number exists is an open problem, so the statement is proved
here in conditional (reduced) form: given `a ≥ 1` and an odd `m ≥ 1` satisfying the
"odd part" equation `(2 ^ a + 1) σ*(m) = 2 ^ (a+1) m`, with `2 ^ a * m` different from the five
known unitary perfect numbers, a sixth unitary perfect number exists.

By `sixth_exists_iff` this hypothesis is not merely sufficient but also necessary, so the
reduction loses nothing: the search for a sixth unitary perfect number is exactly the search
for such a pair `(a, m)`. -/
theorem SixthUnitaryPerfectExists
    (h : ∃ a m : ℕ, 1 ≤ a ∧ Odd m ∧ 0 < m ∧
      (2 ^ a + 1) * sigmaStar m = 2 ^ (a + 1) * m ∧ 2 ^ a * m ∉ knownUnitaryPerfect) :
    ∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect :=
  sixth_exists_iff.2 h

end Brockian.UnitaryPerfect

