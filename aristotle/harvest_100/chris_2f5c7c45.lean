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

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: divisors `d` with `gcd (d, n / d) = 1`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- The sum of the unitary divisors of `n`, usually written `σ*(n)`. -/
def usigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is unitary perfect if it is positive and `σ*(n) = 2n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ usigma n = 2 * n

/-- The five known unitary perfect numbers. -/
def knownUnitaryPerfect : Finset ℕ :=
  {6, 60, 90, 87360, 146361946186458562560000}

instance (n : ℕ) : Decidable (IsUnitaryPerfect n) := by
  unfold IsUnitaryPerfect; infer_instance

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ (d ∣ n ∧ n ≠ 0) ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

lemma ne_zero_of_mem_unitaryDivisors {n d : ℕ} (hd : d ∈ unitaryDivisors n) : d ≠ 0 := by
  rw [mem_unitaryDivisors] at hd
  exact fun h => hd.1.2 (by simpa [h] using hd.1.1)

/-- `n` is the product of its maximal prime powers. -/
lemma prod_primeFactors_pow_factorization {n : ℕ} (h : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self h]
  rw [Nat.prod_factorization_eq_prod_primeFactors]

/-- The prime factorisation of a unitary divisor agrees with that of `n`
at every prime dividing it. -/
lemma factorization_eq_of_mem_unitaryDivisors {n d p : ℕ}
    (hd : d ∈ unitaryDivisors n) (hp : p ∈ d.primeFactors) :
    d.factorization p = n.factorization p := by
  rw [mem_unitaryDivisors] at hd
  obtain ⟨⟨hdvd, hn⟩, hcop⟩ := hd
  obtain ⟨hpp, hpd, hd0⟩ := Nat.mem_primeFactors.mp hp
  have hq0 : n / d ≠ 0 := by
    intro h
    rw [Nat.div_eq_zero_iff] at h
    rcases h with h | h
    · exact hd0 h
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (by omega)
  have hnd : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
  have hpq : ¬ p ∣ (n / d) := by
    intro h
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpd hcop) h
    exact hpp.one_lt.ne' this
  rw [hnd, Nat.factorization_mul hd0 hq0]
  simp [Nat.factorization_eq_zero_of_not_dvd hpq]

/-- The prime factors of a product of prime powers with nonzero exponents. -/
lemma primeFactors_prod_pow {t : Finset ℕ} {e : ℕ → ℕ}
    (hp : ∀ p ∈ t, p.Prime) (he : ∀ p ∈ t, e p ≠ 0) :
    (∏ p ∈ t, p ^ e p).primeFactors = t := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rw [Nat.primeFactors_mul (pow_ne_zero _ (hp a (by simp)).ne_zero)
        (Finset.prod_ne_zero_iff.mpr fun p hp' =>
          pow_ne_zero _ (hp p (by simp [hp'])).ne_zero)]
      rw [Nat.primeFactors_pow _ (he a (by simp)), (hp a (by simp)).primeFactors]
      rw [ih (fun p hp' => hp p (by simp [hp'])) (fun p hp' => he p (by simp [hp']))]
      simp

/-- A product of the maximal prime powers over a subset of the prime factors of `n`
is a unitary divisor of `n`. -/
lemma prod_pow_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) :
    (∏ p ∈ t, p ^ n.factorization p) ∈ unitaryDivisors n := by
  classical
  set d := ∏ p ∈ t, p ^ n.factorization p with hd
  set c := ∏ p ∈ n.primeFactors \ t, p ^ n.factorization p with hc
  have hprod : c * d = n := by
    rw [hc, hd, Finset.prod_sdiff ht, prod_primeFactors_pow_factorization hn]
  have hcop : Nat.Coprime d c := by
    refine Nat.Coprime.prod_left fun p hpt => Nat.Coprime.prod_right fun q hq => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (ht hpt)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
    refine Nat.Coprime.pow _ _ ?_
    rw [Nat.coprime_primes hpp hqp]
    rintro rfl
    exact (Finset.mem_sdiff.mp hq).2 hpt
  have hdvd : d ∣ n := ⟨c, by rw [← hprod]; ring⟩
  have hd0 : d ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (ht hp)).ne_zero
  have hdiv : n / d = c := by
    rw [← hprod, Nat.mul_div_assoc _ (dvd_refl d), Nat.div_self (Nat.pos_of_ne_zero hd0), mul_one]
  rw [mem_unitaryDivisors, hdiv]
  exact ⟨⟨hdvd, hn⟩, hcop⟩

lemma primeFactors_subset_of_mem_unitaryDivisors {n d : ℕ} (hd : d ∈ unitaryDivisors n) :
    d.primeFactors ⊆ n.primeFactors := by
  rw [mem_unitaryDivisors] at hd
  exact Nat.primeFactors_mono hd.1.1 hd.1.2

/-- Every unitary divisor is the product of the maximal prime powers over its prime factors. -/
lemma prod_pow_primeFactors_of_mem_unitaryDivisors {n d : ℕ} (hd : d ∈ unitaryDivisors n) :
    (∏ p ∈ d.primeFactors, p ^ n.factorization p) = d := by
  calc (∏ p ∈ d.primeFactors, p ^ n.factorization p)
      = ∏ p ∈ d.primeFactors, p ^ d.factorization p :=
        Finset.prod_congr rfl fun p hp => by
          rw [factorization_eq_of_mem_unitaryDivisors hd hp]
    _ = d := prod_primeFactors_pow_factorization (ne_zero_of_mem_unitaryDivisors hd)

/-- The product formula `σ*(n) = ∏_{p ∣ n} (p^{v_p(n)} + 1)`. -/
theorem usigma_eq_prod {n : ℕ} (hn : n ≠ 0) :
    usigma n = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
  classical
  rw [Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one]
  rw [usigma]
  refine Finset.sum_nbij' (fun d => d.primeFactors) (fun t => ∏ p ∈ t, p ^ n.factorization p)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    exact Finset.mem_powerset.mpr (primeFactors_subset_of_mem_unitaryDivisors hd)
  · intro t ht
    exact prod_pow_mem_unitaryDivisors hn (Finset.mem_powerset.mp ht)
  · intro d hd
    exact prod_pow_primeFactors_of_mem_unitaryDivisors hd
  · intro t ht
    refine primeFactors_prod_pow
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)) fun p hp => ?_
    have h1 := Finset.mem_powerset.mp ht hp
    rw [← Nat.support_factorization] at h1
    exact Finsupp.mem_support_iff.mp h1
  · intro d hd
    exact (prod_pow_primeFactors_of_mem_unitaryDivisors hd).symm

@[simp] lemma usigma_one : usigma 1 = 1 := by
  decide

/-- `σ*` at a prime power. -/
theorem usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    usigma (p ^ k) = p ^ k + 1 := by
  rw [usigma_eq_prod (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_pow _ hk, hp.primeFactors]
  simp [Nat.Prime.factorization_pow hp]

/-- `σ*` is multiplicative. -/
theorem usigma_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  have key : ∀ {a b : ℕ}, Nat.Coprime a b → ∀ p ∈ a.primeFactors, b.factorization p = 0 := by
    intro a b hab p hp
    refine Nat.factorization_eq_zero_of_not_dvd fun hdvd => ?_
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
    have hc : Nat.Coprime p p := (hab.coprime_dvd_left hpa).coprime_dvd_right hdvd
    exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (hc.eq_one_of_dvd dvd_rfl)
  rw [usigma_eq_prod (mul_ne_zero hm hn), usigma_eq_prod hm, usigma_eq_prod hn,
    h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]
  congr 1
  · exact Finset.prod_congr rfl fun p hp => by
      rw [Nat.factorization_mul hm hn]; simp [key h p hp]
  · exact Finset.prod_congr rfl fun p hp => by
      rw [Nat.factorization_mul hm hn]; simp [key h.symm p hp]

lemma usigma_mul_prime_pow {m p k : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hk : k ≠ 0)
    (hd : ¬ p ∣ m) : usigma (m * p ^ k) = usigma m * (p ^ k + 1) := by
  rw [usigma_mul_of_coprime hm (pow_ne_zero _ hp.ne_zero)
    (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd).symm),
    usigma_prime_pow hp hk]

lemma usigma_mul_prime {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hd : ¬ p ∣ m) :
    usigma (m * p) = usigma m * (p + 1) := by
  simpa using usigma_mul_prime_pow (k := 1) hm hp one_ne_zero hd

/-- No prime power is unitary perfect. -/
theorem not_isUnitaryPerfect_prime_pow {p k : ℕ} (hp : p.Prime) :
    ¬ IsUnitaryPerfect (p ^ k) := by
  rintro ⟨hpos, heq⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at heq
  · rw [usigma_prime_pow hp hk.ne'] at heq
    have h2 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
    omega

/-- A unitary perfect number has at least two distinct prime factors. -/
theorem two_le_card_primeFactors {n : ℕ} (h : IsUnitaryPerfect n) :
    2 ≤ n.primeFactors.card := by
  obtain ⟨hpos, heq⟩ := h
  by_contra hc
  push_neg at hc
  interval_cases hcard : n.primeFactors.card
  · have hemp : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard
    rw [Nat.primeFactors_eq_empty] at hemp
    rcases hemp with rfl | rfl
    · omega
    · simp at heq
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
    have hn : n = p ^ n.factorization p := by
      conv_lhs => rw [← prod_primeFactors_pow_factorization hpos.ne']
      rw [hp, Finset.prod_singleton]
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; simp)
    exact not_isUnitaryPerfect_prime_pow (k := n.factorization p) hpp (hn ▸ ⟨hpos, heq⟩)

/-- Every unitary perfect number is even. -/
theorem even_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  obtain ⟨hpos, heq⟩ := h
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hcard := two_le_card_primeFactors ⟨hpos, heq⟩
  have hdvd : (∏ _p ∈ n.primeFactors, 2) ∣ ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
    refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
    have hoddp : Odd (p ^ n.factorization p) := (hpp.odd_of_ne_two hp2).pow
    exact even_iff_two_dvd.mp (Odd.add_one hoddp)
  rw [Finset.prod_const, ← usigma_eq_prod hpos.ne', heq] at hdvd
  have h4 : (2 : ℕ) ^ 2 ∣ 2 ^ n.primeFactors.card := pow_dvd_pow 2 hcard
  have h5 : (4 : ℕ) ∣ 2 * n := by simpa using h4.trans hdvd
  obtain ⟨c, hc⟩ := h5
  rw [Nat.odd_iff] at hodd
  omega

/-- For a unitary perfect number, the number of distinct prime factors is at most
`v₂(n) + 2`, where `v₂(n)` is the exponent of `2` in `n`. -/
theorem card_primeFactors_le_factorization_two_add_two {n : ℕ} (h : IsUnitaryPerfect n) :
    n.primeFactors.card ≤ n.factorization 2 + 2 := by
  obtain ⟨hpos, heq⟩ := h
  have hn0 : n ≠ 0 := hpos.ne'
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two,
      (even_iff_two_dvd.mp (even_of_isUnitaryPerfect ⟨hpos, heq⟩)), hn0⟩
  have hdvd : (2 : ℕ) ^ (n.primeFactors.card - 1) ∣ usigma n := by
    rw [usigma_eq_prod hn0, ← Finset.prod_erase_mul _ _ h2]
    refine Dvd.dvd.mul_right ?_ _
    have hcard : (n.primeFactors.erase 2).card = n.primeFactors.card - 1 :=
      Finset.card_erase_of_mem h2
    rw [← hcard, ← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    exact even_iff_two_dvd.mp (Odd.add_one ((hpp.odd_of_ne_two (Finset.ne_of_mem_erase hp)).pow))
  rw [heq] at hdvd
  have hfac : (2 * n).factorization 2 = 1 + n.factorization 2 := by
    rw [Nat.factorization_mul (by norm_num) hn0]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by positivity)).mp hdvd
  rw [hfac] at hle
  have h1 : 1 ≤ n.primeFactors.card := Finset.card_pos.mpr ⟨2, h2⟩
  omega

lemma factorization_ne_zero_of_mem_primeFactors {n p : ℕ} (h : p ∈ n.primeFactors) :
    n.factorization p ≠ 0 := by
  rw [← Nat.support_factorization] at h
  exact Finsupp.mem_support_iff.mp h

/-- The only unitary perfect number with exactly two distinct prime factors is `6`. -/
theorem eq_six_of_card_primeFactors_eq_two {n : ℕ} (h : IsUnitaryPerfect n)
    (hcard : n.primeFactors.card = 2) : n = 6 := by
  obtain ⟨hpos, heq⟩ := h
  have hn0 : n ≠ 0 := hpos.ne'
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two,
      (even_iff_two_dvd.mp (even_of_isUnitaryPerfect ⟨hpos, heq⟩)), hn0⟩
  obtain ⟨p, hset, hp2⟩ : ∃ p, n.primeFactors = {2, p} ∧ p ≠ 2 := by
    obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp hcard
    rw [hs] at h2
    rcases Finset.mem_insert.mp h2 with rfl | hy
    · exact ⟨y, hs, fun h => hxy h.symm⟩
    · rw [Finset.mem_singleton] at hy
      subst hy
      exact ⟨x, by rw [hs, Finset.pair_comm], hxy⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
  have hpmem : p ∈ n.primeFactors := by rw [hset]; simp
  set a := n.factorization 2 with ha
  set b := n.factorization p with hb
  have hne : (2 : ℕ) ≠ p := fun h => hp2 h.symm
  have hn : n = 2 ^ a * p ^ b := by
    conv_lhs => rw [← prod_primeFactors_pow_factorization hn0]
    rw [hset, Finset.prod_pair hne]
  have hus : usigma n = (2 ^ a + 1) * (p ^ b + 1) := by
    rw [usigma_eq_prod hn0, hset, Finset.prod_pair hne]
  have ha1 : a ≠ 0 := factorization_ne_zero_of_mem_primeFactors h2
  have hb1 : b ≠ 0 := factorization_ne_zero_of_mem_primeFactors hpmem
  have hA : 2 ≤ 2 ^ a := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  have hB : 3 ≤ p ^ b := by
    calc (3 : ℕ) ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ b := Nat.pow_le_pow_right (by omega) (by omega)
  rw [hus, hn] at heq
  set A := 2 ^ a with hAdef
  set B := p ^ b with hBdef
  have key : (A - 1) * (B - 1) = 2 := by
    have h1 : A + 1 = (A - 1) + 2 := by omega
    have h2' : B + 1 = (B - 1) + 2 := by omega
    have h3 : A = (A - 1) + 1 := by omega
    have h4 : B = (B - 1) + 1 := by omega
    rw [h1, h2'] at heq
    nlinarith [heq, h3, h4]
  have hle : A - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨B - 1, key.symm⟩
  have h2A : 2 ∣ A := dvd_pow_self 2 ha1
  have hAeq : A = 2 := by
    rcases (show A - 1 = 1 ∨ A - 1 = 2 by
      rcases Nat.eq_zero_or_pos (A - 1) with h | h
      · rw [h] at key; simp at key
      · omega) with h | h
    · omega
    · exfalso
      have h3A : A = 3 := by omega
      rw [h3A] at h2A
      omega
  have hBeq : B = 3 := by
    rw [hAeq] at key
    omega
  rw [hn, hAeq, hBeq]

lemma isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  refine ⟨by norm_num, ?_⟩
  have e : (87360 : ℕ) = 2 ^ 6 * 3 * 5 * 7 * 13 := by norm_num
  rw [e]
  rw [usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_prime_pow Nat.prime_two (by norm_num)]
  norm_num

set_option maxRecDepth 4000 in
lemma isUnitaryPerfect_fifth : IsUnitaryPerfect 146361946186458562560000 := by
  refine ⟨by norm_num, ?_⟩
  have e : (146361946186458562560000 : ℕ)
      = 2 ^ 18 * 3 * 5 ^ 4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313 := by norm_num
  rw [e]
  rw [usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      usigma_mul_prime (by norm_num) (by norm_num) (by norm_num),
      usigma_prime_pow Nat.prime_two (by norm_num)]
  norm_num

/-- The five known unitary perfect numbers really are unitary perfect. -/
theorem isUnitaryPerfect_of_mem_known {n : ℕ} (hn : n ∈ knownUnitaryPerfect) :
    IsUnitaryPerfect n := by
  simp only [knownUnitaryPerfect, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by decide⟩
  · exact ⟨by norm_num, by decide⟩
  · exact ⟨by norm_num, by decide⟩
  · exact isUnitaryPerfect_87360
  · exact isUnitaryPerfect_fifth

set_option maxRecDepth 10000 in
/-- There is no unitary perfect number below `91` other than `6`, `60` and `90`. -/
theorem lt_91_isUnitaryPerfect {n : ℕ} (hn : n < 91) (h : IsUnitaryPerfect n) :
    n = 6 ∨ n = 60 ∨ n = 90 := by
  have key : ∀ m ∈ Finset.range 91, IsUnitaryPerfect m → m = 6 ∨ m = 60 ∨ m = 90 := by decide
  exact key n (Finset.mem_range.mpr hn) h

/-- **Conditional reduction for the sixth unitary perfect number.**

Whether a unitary perfect number other than the five known ones exists is open.
This theorem is a Lean-checked reduction: such a "sixth" unitary perfect number exists
if and only if there is a unitary perfect number outside the known list that is even,
exceeds `90`, has at least three distinct prime factors, and whose number of distinct
prime factors is at most `v₂(n) + 2`. -/
theorem SixthUnitaryPerfectExists :
    (∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect) ↔
      (∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect ∧ Even n ∧ 90 < n ∧
        3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ n.factorization 2 + 2) := by
  constructor
  · rintro ⟨n, hn, hnot⟩
    have hsix : n ≠ 6 := by rintro rfl; exact hnot (by simp [knownUnitaryPerfect])
    refine ⟨n, hn, hnot, even_of_isUnitaryPerfect hn, ?_, ?_,
      card_primeFactors_le_factorization_two_add_two hn⟩
    · by_contra hle
      push_neg at hle
      rcases lt_91_isUnitaryPerfect (by omega) hn with rfl | rfl | rfl <;>
        exact hnot (by simp [knownUnitaryPerfect])
    · have h2 := two_le_card_primeFactors hn
      rcases Nat.lt_or_ge n.primeFactors.card 3 with hlt | hge
      · exact absurd (eq_six_of_card_primeFactors_eq_two hn (by omega)) hsix
      · exact hge
  · rintro ⟨n, hn, hnot, -, -, -, -⟩
    exact ⟨n, hn, hnot⟩

end Brockian.UnitaryPerfect

