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
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- `d` is a *unitary divisor* of `n` if `d ∣ n` and `d` is coprime to `n / d`. -/
def IsUnitaryDivisor (d n : ℕ) : Prop := d ∣ n ∧ Nat.Coprime d (n / d)

/-- The finset of unitary divisors of `n`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- The unitary divisor sum `σ*(n)`. -/
def usigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is *unitary perfect* if it is positive and `σ*(n) = 2 * n`, i.e. `n` is the sum of
its proper unitary divisors. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ usigma n = 2 * n

/-- The five known unitary perfect numbers. -/
def knownUnitaryPerfect : Finset ℕ :=
  {6, 60, 90, 87360, 146361946186458562560000}

section Basic

lemma mem_unitaryDivisors {d n : ℕ} (hn : n ≠ 0) :
    d ∈ unitaryDivisors n ↔ IsUnitaryDivisor d n := by
  simp [unitaryDivisors, Nat.mem_divisors, hn, IsUnitaryDivisor]

/-- Every positive natural number is the product of the prime powers occurring in it. -/
lemma prod_primeFactors_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Nat.prod_primeFactors_prod_factorization]
  exact Finsupp.prod_congr (fun p _ => rfl)

/-- The prime factors of `∏ p ∈ S, p ^ (n.factorization p)` are exactly `S`, for
`S ⊆ n.primeFactors`. -/
lemma primeFactors_prod_pow {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hsub : s ⊆ n.primeFactors := fun x hx => hS (mem_insert_of_mem hx)
      have hamem : a ∈ n.primeFactors := hS (mem_insert_self a s)
      have hap : a.Prime := Nat.prime_of_mem_primeFactors hamem
      have hafac : n.factorization a ≠ 0 := by
        have := (Nat.mem_primeFactors.mp hamem)
        simpa [Nat.factorization_eq_zero_iff, hap.ne_one, this.2.2] using
          (Nat.Prime.factorization_pos_of_dvd hap this.2.2 this.2.1).ne'
      have hne : (a ^ n.factorization a) ≠ 0 := pow_ne_zero _ hap.pos.ne'
      have hne2 : (∏ p ∈ s, p ^ n.factorization p) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro p hp
        exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hsub hp)).pos.ne'
      rw [Finset.prod_insert ha, Nat.primeFactors_mul hne hne2, ih hsub,
        Nat.primeFactors_prime_pow hafac hap]
      simp

lemma prod_pow_coprime_prod_pow {n : ℕ} {S T : Finset ℕ} (hS : S ⊆ n.primeFactors)
    (hT : T ⊆ n.primeFactors) (hdisj : Disjoint S T) :
    Nat.Coprime (∏ p ∈ S, p ^ n.factorization p) (∏ p ∈ T, p ^ n.factorization p) := by
  refine Nat.Coprime.prod_left (fun p hp => Nat.Coprime.prod_right (fun q hq => ?_))
  have hpq : p ≠ q := by
    rintro rfl
    exact (Finset.disjoint_left.mp hdisj hp) hq
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hS hp))
    (Nat.prime_of_mem_primeFactors (hT hq))).mpr hpq)

/-- The unitary divisors of `n` are exactly the products `∏ p ∈ S, p ^ (n.factorization p)`
over subsets `S` of the prime factors of `n`. -/
lemma unitaryDivisors_eq_image {n : ℕ} (hn : n ≠ 0) :
    unitaryDivisors n =
      n.primeFactors.powerset.image (fun S => ∏ p ∈ S, p ^ n.factorization p) := by
  ext d
  simp only [mem_image, mem_powerset, mem_unitaryDivisors hn, IsUnitaryDivisor]
  constructor
  · rintro ⟨hdvd, hcop⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hn (Nat.eq_zero_of_zero_dvd hdvd)
    have hq0 : n / d ≠ 0 := by
      rintro h
      exact hn (by rw [← Nat.div_mul_cancel hdvd, h, zero_mul])
    have hfac : ∀ p ∈ d.primeFactors, d.factorization p = n.factorization p := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hnotdvd : ¬ p ∣ n / d := by
        intro hcontra
        have : p ∣ Nat.gcd d (n / d) := Nat.dvd_gcd hpd hcontra
        rw [hcop] at this
        exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
      have hsplit : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
      have := congrArg (fun f => f p) (congrArg Nat.factorization hsplit)
      simp only [Nat.factorization_mul hd0 hq0, Finsupp.add_apply] at this
      rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd] at this
      omega
    refine ⟨d.primeFactors, Nat.primeFactors_mono hdvd hn, ?_⟩
    calc ∏ p ∈ d.primeFactors, p ^ n.factorization p
        = ∏ p ∈ d.primeFactors, p ^ d.factorization p := by
          refine Finset.prod_congr rfl (fun p hp => ?_)
          rw [hfac p hp]
      _ = d := prod_primeFactors_pow_factorization hd0
  · rintro ⟨S, hS, rfl⟩
    set d := ∏ p ∈ S, p ^ n.factorization p with hd
    set e := ∏ p ∈ n.primeFactors \ S, p ^ n.factorization p with he
    have hde : d * e = n := by
      rw [hd, he, mul_comm, Finset.prod_sdiff hS, prod_primeFactors_pow_factorization hn]
    have hd0 : 0 < d := by
      refine Finset.prod_pos (fun p hp => ?_)
      exact pow_pos (Nat.prime_of_mem_primeFactors (hS hp)).pos _
    have hdvd : d ∣ n := ⟨e, hde.symm⟩
    have hdiv : n / d = e := by
      rw [← hde, Nat.mul_div_cancel_left _ hd0]
    refine ⟨hdvd, ?_⟩
    rw [hdiv]
    exact prod_pow_coprime_prod_pow hS (Finset.sdiff_subset) (Finset.disjoint_sdiff)

/-- Euler-product formula for the unitary divisor sum. -/
lemma usigma_eq_prod {n : ℕ} (hn : n ≠ 0) :
    usigma n = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
  have hinj : Set.InjOn (fun S => ∏ p ∈ S, p ^ n.factorization p)
      (↑n.primeFactors.powerset : Set (Finset ℕ)) := by
    intro S hS T hT h
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff] at hS hT
    have hS' : S ⊆ n.primeFactors := by
      intro x hx
      have := hS (by simpa using hx)
      simpa using this
    have hT' : T ⊆ n.primeFactors := by
      intro x hx
      have := hT (by simpa using hx)
      simpa using this
    rw [← primeFactors_prod_pow hS', ← primeFactors_prod_pow hT']
    exact congrArg Nat.primeFactors h
  rw [usigma, unitaryDivisors_eq_image hn, Finset.sum_image hinj]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  simp

lemma usigma_one : usigma 1 = 1 := by
  rw [usigma_eq_prod one_ne_zero]
  simp

lemma usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    usigma (p ^ k) = p ^ k + 1 := by
  rw [usigma_eq_prod (pow_ne_zero _ hp.pos.ne'), Nat.primeFactors_prime_pow hk hp]
  simp [Nat.Prime.factorization_pow hp]

lemma usigma_prime {p : ℕ} (hp : p.Prime) : usigma p = p + 1 := by
  simpa using usigma_prime_pow hp (k := 1) one_ne_zero

/-- `σ*` is multiplicative. -/
lemma usigma_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  have hdisj : Disjoint m.primeFactors n.primeFactors :=
    Nat.Coprime.disjoint_primeFactors h
  rw [usigma_eq_prod (mul_ne_zero hm hn), usigma_eq_prod hm, usigma_eq_prod hn,
    Nat.primeFactors_mul hm hn, Finset.prod_union hdisj]
  congr 1
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Nat.factorization_mul hm hn]
    simp only [Finsupp.add_apply]
    have : n.factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd (fun hcontra => ?_)
      exact (Finset.disjoint_left.mp hdisj hp)
        (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hcontra, hn⟩)
    rw [this, add_zero]
  · refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Nat.factorization_mul hm hn]
    simp only [Finsupp.add_apply]
    have : m.factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd (fun hcontra => ?_)
      exact (Finset.disjoint_right.mp hdisj hp)
        (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hcontra, hm⟩)
    rw [this]
    simp

end Basic

section Structure

lemma one_lt_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : 1 < n := by
  rcases h with ⟨hpos, heq⟩
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    · simp [usigma_one] at heq
  · omega

/-- If `n` is unitary perfect, then its number of odd prime factors is at most
`v₂(n) + 1`, where `v₂` denotes the 2-adic valuation. -/
lemma card_odd_primeFactors_le {n : ℕ} (h : IsUnitaryPerfect n) :
    (n.primeFactors.erase 2).card ≤ n.factorization 2 + 1 := by
  obtain ⟨hpos, heq⟩ := h
  have hn : n ≠ 0 := hpos.ne'
  set k := (n.primeFactors.erase 2).card with hk
  -- `2 ^ k` divides the odd part of the product formula
  have hdvd_sub : (2 : ℕ) ^ k ∣ ∏ p ∈ n.primeFactors.erase 2, (p ^ n.factorization p + 1) := by
    rw [hk, ← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ (fun p hp => ?_)
    have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
    have hpmem : p ∈ n.primeFactors := Finset.mem_of_mem_erase hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hodd : Odd p := hpp.odd_of_ne_two hp2
    have : Odd (p ^ n.factorization p) := hodd.pow
    obtain ⟨t, ht⟩ := this
    exact ⟨t + 1, by omega⟩
  have hdvd : (2 : ℕ) ^ k ∣ usigma n := by
    rw [usigma_eq_prod hn]
    exact hdvd_sub.trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _))
  rw [heq] at hdvd
  have h2n : (2 * n) ≠ 0 := by positivity
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h2n).mp hdvd
  rwa [Nat.factorization_mul two_ne_zero hn, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, add_comm] at this

/-- There is no odd unitary perfect number: every unitary perfect number is even. -/
lemma even_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  obtain ⟨hpos, heq⟩ := h
  have hn : n ≠ 0 := hpos.ne'
  have h1 : 1 < n := one_lt_of_isUnitaryPerfect ⟨hpos, heq⟩
  by_contra hodd
  have hnodd : ¬ (2 ∣ n) := fun hc => hodd ((even_iff_exists_two_nsmul n).mpr (by
    obtain ⟨c, rfl⟩ := hc
    exact ⟨c, by simp [two_mul]⟩))
  have h2notmem : 2 ∉ n.primeFactors := fun hc => hnodd (Nat.dvd_of_mem_primeFactors hc)
  have herase : n.primeFactors.erase 2 = n.primeFactors := Finset.erase_eq_self.mpr h2notmem
  have hfac2 : n.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hnodd
  have hcard := card_odd_primeFactors_le ⟨hpos, heq⟩
  rw [herase, hfac2] at hcard
  -- `n` has at least one prime factor, hence exactly one
  have hne : n.primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    exact h1
  have hcard1 : n.primeFactors.card = 1 := by
    have := Finset.card_pos.mpr hne
    omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard1
  have hnp : n = p ^ n.factorization p := by
    have := prod_primeFactors_pow_factorization hn
    rw [hp] at this
    simpa using this.symm
  have hsig : usigma n = p ^ n.factorization p + 1 := by
    rw [usigma_eq_prod hn, hp]
    simp
  have hfin : p ^ n.factorization p + 1 = 2 * n := by rw [← hsig, heq]
  rw [← hnp] at hfin
  omega

end Structure

section Known

lemma isUnitaryPerfect_six : IsUnitaryPerfect 6 := by
  refine ⟨by norm_num, ?_⟩
  have : (6 : ℕ) = 2 * 3 := by norm_num
  rw [this, usigma_mul_of_coprime two_ne_zero three_ne_zero (by decide),
    usigma_prime Nat.prime_two, usigma_prime Nat.prime_three]

lemma isUnitaryPerfect_sixty : IsUnitaryPerfect 60 := by
  refine ⟨by norm_num, ?_⟩
  have h : (60 : ℕ) = 2 ^ 2 * (3 * 5) := by norm_num
  rw [h, usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_prime_pow Nat.prime_two two_ne_zero,
    usigma_prime Nat.prime_three, usigma_prime (by norm_num)]
  norm_num

lemma isUnitaryPerfect_ninety : IsUnitaryPerfect 90 := by
  refine ⟨by norm_num, ?_⟩
  have h : (90 : ℕ) = 2 * (3 ^ 2 * 5) := by norm_num
  rw [h, usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_prime Nat.prime_two,
    usigma_prime_pow Nat.prime_three two_ne_zero, usigma_prime (by norm_num)]
  norm_num

lemma isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  refine ⟨by norm_num, ?_⟩
  have h : (87360 : ℕ) = 2 ^ 6 * (3 * (5 * (7 * 13))) := by norm_num
  rw [h, usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_prime_pow Nat.prime_two (by norm_num),
    usigma_prime Nat.prime_three, usigma_prime (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num)]
  norm_num

lemma isUnitaryPerfect_big : IsUnitaryPerfect 146361946186458562560000 := by
  refine ⟨by norm_num, ?_⟩
  have h : (146361946186458562560000 : ℕ) =
      2 ^ 18 * (3 * (5 ^ 4 * (7 * (11 * (13 * (19 * (37 * (79 * (109 * (157 * 313)))))))))) := by
    norm_num
  rw [h, usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_mul_of_coprime (by norm_num) (by norm_num) (by decide),
    usigma_prime_pow Nat.prime_two (by norm_num),
    usigma_prime Nat.prime_three,
    usigma_prime_pow (by norm_num) (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num), usigma_prime (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num), usigma_prime (by norm_num),
    usigma_prime (by norm_num), usigma_prime (by norm_num), usigma_prime (by norm_num)]
  norm_num

/-- The five known unitary perfect numbers really are unitary perfect. -/
lemma isUnitaryPerfect_of_mem_known {n : ℕ} (hn : n ∈ knownUnitaryPerfect) :
    IsUnitaryPerfect n := by
  simp only [knownUnitaryPerfect, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact isUnitaryPerfect_six
  · exact isUnitaryPerfect_sixty
  · exact isUnitaryPerfect_ninety
  · exact isUnitaryPerfect_87360
  · exact isUnitaryPerfect_big

end Known

/--
**Conditional reduction for the existence of a sixth unitary perfect number.**

Whether a sixth unitary perfect number exists (i.e. a unitary perfect number besides
`6, 60, 90, 87360, 146361946186458562560000`) is an open problem.  What is proved here
unconditionally is a reduction: a sixth unitary perfect number exists if and only if
there is a unitary perfect number outside the known list which is moreover *even* and
whose number of odd prime factors is at most `v₂(n) + 1`.  Equivalently, any sixth
unitary perfect number automatically satisfies these two structural constraints.
-/
theorem SixthUnitaryPerfectExists :
    (∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect) ↔
      (∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect ∧ Even n ∧
        (n.primeFactors.erase 2).card ≤ n.factorization 2 + 1) := by
  constructor
  · rintro ⟨n, hn, hn'⟩
    exact ⟨n, hn, hn', even_of_isUnitaryPerfect hn, card_odd_primeFactors_le hn⟩
  · rintro ⟨n, hn, hn', -, -⟩
    exact ⟨n, hn, hn'⟩

end Brockian.UnitaryPerfect

