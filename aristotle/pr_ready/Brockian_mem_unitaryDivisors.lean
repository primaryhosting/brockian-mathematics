/-!
# Mem Unitary Divisors
Category: Brockian External
Target: Brockian.mem_unitaryDivisors
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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


/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *unitary divisor* of `n` is a divisor `d ∣ n` with `gcd d (n / d) = 1`, and `n` is
*unitary perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.
Exactly five unitary perfect numbers are known,

```
6, 60, 90, 87360, 146361946186458562560000
```

and whether a sixth one exists is a well-known open problem.  Consequently the statement
"a sixth unitary perfect number exists" cannot be proved outright; what is established
here is:

* the multiplicative theory of `σ*` from scratch, culminating in the Euler-product
  formula `sigmaStar_eq_prod_primeFactors` and multiplicativity
  `sigmaStar_mul_of_coprime`;
* unconditional verification that the five known numbers are unitary perfect
  (`known_isUnitaryPerfect`);
* unconditional structural theorems: every unitary perfect number has an odd prime
  factor (`exists_odd_prime_factor`) and is even (`even_of_isUnitaryPerfect`), i.e.
  there are no odd unitary perfect numbers, and a unitary perfect number with only two
  distinct prime factors must equal `6` (`eq_six_of_card_primeFactors_eq_two`);
* the target theorem `SixthUnitaryPerfectExists`, a Lean-checked *conditional
  reduction*: from the existence of a unitary perfect number outside the known list one
  obtains a genuine "sixth" unitary perfect number together with all of the structural
  information above (even, `> 6`, at least three distinct prime factors, divisible by an
  odd prime).

Mathlib search note: `exact?` / `apply?` / `rw?` find nothing directly applicable here.
Mathlib's divisor API (`Nat.divisors`, `Nat.ArithmeticFunction.sigma`,
`Nat.ArithmeticFunction.isMultiplicative_sigma`) treats ordinary divisors only and has no
notion of unitary divisor, so the theory below is built from the general factorization
lemmas (`Nat.factorization_prod_pow_eq_self`, `Finset.prod_add`, ...).
-/

open Finset

namespace Brockian
namespace UnitaryPerfect

/-- The unitary divisors of `n`: the divisors `d` of `n` with `d` coprime to `n / d`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => Nat.Coprime d (n / d))

/-- `σ*(n)`, the sum of the unitary divisors of `n`. -/
def sigmaStar (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- `n` is unitary perfect if it is positive and `σ*(n) = 2n`. -/
def IsUnitaryPerfect (n : ℕ) : Prop := 0 < n ∧ sigmaStar n = 2 * n

/-- The five known unitary perfect numbers. -/
def known : Finset ℕ := {6, 60, 90, 87360, 146361946186458562560000}

section Formula

variable {n : ℕ}

lemma mem_unitaryDivisors {d n : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors, Nat.mem_divisors, and_assoc]

/-- The full prime-power decomposition of `n` recovers `n`. -/
lemma prod_primeFactors_pow (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]

lemma coprime_pow_prod {p a : ℕ} {T : Finset ℕ} (hp : p.Prime)
    (hT : ∀ q ∈ T, q.Prime) (hpT : p ∉ T) (e : ℕ → ℕ) :
    Nat.Coprime (p ^ a) (∏ q ∈ T, q ^ e q) := by
  refine Nat.Coprime.prod_right fun q hq => ?_
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp (hT q hq)).2 (by rintro rfl; exact hpT hq))

/-- The prime factors of a partial prime-power product are exactly the chosen primes. -/
lemma primeFactors_partProd {S : Finset ℕ} (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, p ^ n.factorization p).primeFactors = S := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert p T hpT ih =>
      have hpS : p ∈ n.primeFactors := hS (mem_insert_self _ _)
      obtain ⟨hp, hpd, hn0⟩ := Nat.mem_primeFactors.1 hpS
      have hTsub : T ⊆ n.primeFactors := fun q hq => hS (mem_insert_of_mem hq)
      have hcop : Nat.Coprime (p ^ n.factorization p) (∏ q ∈ T, q ^ n.factorization q) :=
        coprime_pow_prod hp (fun q hq => Nat.prime_of_mem_primeFactors (hTsub hq)) hpT _
      rw [Finset.prod_insert hpT, hcop.primeFactors_mul, ih hTsub,
        Nat.primeFactors_prime_pow (Nat.Prime.factorization_pos_of_dvd hp hn0 hpd).ne' hp]
      exact (Finset.insert_eq p T).symm

/-- The unitary divisors of `n` are exactly the products of full prime powers taken over a
subset of the prime factors of `n`. -/
lemma unitaryDivisors_eq_image (hn : n ≠ 0) :
    unitaryDivisors n =
      n.primeFactors.powerset.image (fun S => ∏ p ∈ S, p ^ n.factorization p) := by
  classical
  ext d
  simp only [Finset.mem_image, Finset.mem_powerset, mem_unitaryDivisors]
  constructor
  · rintro ⟨hdvd, -, hcop⟩
    have hd0 : d ≠ 0 := by rintro rfl; simp at hdvd; exact hn hdvd
    refine ⟨d.primeFactors, Nat.primeFactors_mono hdvd hn, ?_⟩
    have key : ∀ p ∈ d.primeFactors, d.factorization p = n.factorization p := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hnp : ¬ p ∣ (n / d) := by
        intro hdd
        have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd hpd hdd
        exact absurd (Nat.dvd_one.mp hp1) hpp.ne_one
      have h0 : (n / d).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnp
      rw [Nat.factorization_div hdvd] at h0
      simp only [Finsupp.coe_tsub, Pi.sub_apply] at h0
      have hle : d.factorization p ≤ n.factorization p :=
        (Nat.factorization_le_iff_dvd hd0 hn).2 hdvd p
      omega
    calc ∏ p ∈ d.primeFactors, p ^ n.factorization p
        = ∏ p ∈ d.primeFactors, p ^ d.factorization p :=
          Finset.prod_congr rfl fun p hp => by rw [key p hp]
      _ = d := prod_primeFactors_pow hd0
  · rintro ⟨S, hS, rfl⟩
    set d := ∏ p ∈ S, p ^ n.factorization p with hd
    set m := ∏ p ∈ n.primeFactors \ S, p ^ n.factorization p with hm
    have hmul : m * d = n := by
      rw [hm, hd, Finset.prod_sdiff hS, prod_primeFactors_pow hn]
    have hdvd : d ∣ n := ⟨m, by rw [← hmul]; ring⟩
    have hd0 : d ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
      exact pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors (hS hp)))
    have hquot : n / d = m := by
      rw [← hmul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)]
    refine ⟨hdvd, hn, ?_⟩
    rw [hquot, hd, hm]
    refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors (hS hp)
    have hq' : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hq).1
    refine Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' hq').2 ?_)
    rintro rfl
    exact (Finset.mem_sdiff.1 hq).2 hp

/-- The Euler-product formula for `σ*`: `σ*(n) = ∏_{p ∣ n} (p ^ v_p(n) + 1)`. -/
theorem sigmaStar_eq_prod_primeFactors (hn : n ≠ 0) :
    sigmaStar n = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + 1) := by
  classical
  have hinj : Set.InjOn (fun S => ∏ p ∈ S, p ^ n.factorization p) n.primeFactors.powerset := by
    intro S hS T hT h
    have hS' : S ⊆ n.primeFactors := Finset.mem_powerset.1 hS
    have hT' : T ⊆ n.primeFactors := Finset.mem_powerset.1 hT
    have hpf := congrArg Nat.primeFactors h
    rwa [primeFactors_partProd hS', primeFactors_partProd hT'] at hpf
  rw [sigmaStar, unitaryDivisors_eq_image hn, Finset.sum_image hinj]
  rw [Finset.prod_add (fun p => p ^ n.factorization p) (fun _ => 1) n.primeFactors]
  simp

end Formula

section Multiplicative

lemma sigmaStar_one : sigmaStar 1 = 1 := by
  rw [sigmaStar_eq_prod_primeFactors one_ne_zero]; simp

lemma sigmaStar_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    sigmaStar (p ^ k) = p ^ k + 1 := by
  rw [sigmaStar_eq_prod_primeFactors (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow hk hp]
  simp [hp.factorization_pow]

/-- `σ*` is multiplicative. -/
theorem sigmaStar_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.Coprime a b) :
    sigmaStar (a * b) = sigmaStar a * sigmaStar b := by
  classical
  have hdisj : Disjoint a.primeFactors b.primeFactors := Nat.Coprime.disjoint_primeFactors h
  rw [sigmaStar_eq_prod_primeFactors (mul_ne_zero ha hb), sigmaStar_eq_prod_primeFactors ha,
    sigmaStar_eq_prod_primeFactors hb, h.primeFactors_mul,
    Finset.prod_union hdisj, Nat.factorization_mul ha hb]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hz : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (by
      intro hdvd
      exact (Finset.disjoint_left.1 hdisj) hp (Nat.mem_primeFactors.2
        ⟨Nat.prime_of_mem_primeFactors hp, hdvd, hb⟩))
    simp [hz]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hz : a.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (by
      intro hdvd
      exact (Finset.disjoint_right.1 hdisj) hp (Nat.mem_primeFactors.2
        ⟨Nat.prime_of_mem_primeFactors hp, hdvd, ha⟩))
    simp [hz]

/-- Peeling one prime power off a factorization; the workhorse of the numerical
verifications below. -/
lemma sigmaStar_step {p k m N S : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hm : m ≠ 0)
    (hpm : ¬ p ∣ m) (hN : N = p ^ k * m) (hS : sigmaStar m = S) :
    sigmaStar N = (p ^ k + 1) * S := by
  subst hN; subst hS
  have hcop : Nat.Coprime (p ^ k) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  rw [sigmaStar_mul_of_coprime (pow_ne_zero _ hp.ne_zero) hm hcop, sigmaStar_prime_pow hp hk]

end Multiplicative

section KnownExamples

lemma sigmaStar_3 : sigmaStar 3 = 4 := by
  have h := sigmaStar_step (p := 3) (k := 1) (m := 1) (N := 3) (by norm_num) one_ne_zero
    one_ne_zero (by norm_num) (by norm_num) sigmaStar_one
  norm_num at h; exact h

lemma sigmaStar_5 : sigmaStar 5 = 6 := by
  have h := sigmaStar_step (p := 5) (k := 1) (m := 1) (N := 5) (by norm_num) one_ne_zero
    one_ne_zero (by norm_num) (by norm_num) sigmaStar_one
  norm_num at h; exact h

lemma sigmaStar_13 : sigmaStar 13 = 14 := by
  have h := sigmaStar_step (p := 13) (k := 1) (m := 1) (N := 13) (by norm_num) one_ne_zero
    one_ne_zero (by norm_num) (by norm_num) sigmaStar_one
  norm_num at h; exact h

lemma sigmaStar_6 : sigmaStar 6 = 12 := by
  have h := sigmaStar_step (p := 2) (k := 1) (m := 3) (N := 6) (by norm_num) one_ne_zero
    (by norm_num) (by norm_num) (by norm_num) sigmaStar_3
  norm_num at h; exact h

lemma sigmaStar_60 : sigmaStar 60 = 120 := by
  have h15 : sigmaStar 15 = 24 := by
    have h := sigmaStar_step (p := 3) (k := 1) (m := 5) (N := 15) (by norm_num) one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) sigmaStar_5
    norm_num at h; exact h
  have h := sigmaStar_step (p := 2) (k := 2) (m := 15) (N := 60) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h15
  norm_num at h; exact h

lemma sigmaStar_90 : sigmaStar 90 = 180 := by
  have h45 : sigmaStar 45 = 60 := by
    have h := sigmaStar_step (p := 3) (k := 2) (m := 5) (N := 45) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) sigmaStar_5
    norm_num at h; exact h
  have h := sigmaStar_step (p := 2) (k := 1) (m := 45) (N := 90) (by norm_num) one_ne_zero
    (by norm_num) (by norm_num) (by norm_num) h45
  norm_num at h; exact h

lemma sigmaStar_87360 : sigmaStar 87360 = 174720 := by
  have h91 : sigmaStar 91 = 112 := by
    have h := sigmaStar_step (p := 7) (k := 1) (m := 13) (N := 91) (by norm_num) one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) sigmaStar_13
    norm_num at h; exact h
  have h455 : sigmaStar 455 = 672 := by
    have h := sigmaStar_step (p := 5) (k := 1) (m := 91) (N := 455) (by norm_num) one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) h91
    norm_num at h; exact h
  have h1365 : sigmaStar 1365 = 2688 := by
    have h := sigmaStar_step (p := 3) (k := 1) (m := 455) (N := 1365) (by norm_num) one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) h455
    norm_num at h; exact h
  have h := sigmaStar_step (p := 2) (k := 6) (m := 1365) (N := 87360) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h1365
  norm_num at h; exact h

lemma sigmaStar_fifth :
    sigmaStar 146361946186458562560000 = 292723892372917125120000 := by
  have h11 : sigmaStar 313 = 314 := by
    have h := sigmaStar_step (p := 313) (k := 1) (m := 1) (N := 313) (by norm_num) one_ne_zero
      one_ne_zero (by norm_num) (by norm_num) sigmaStar_one
    norm_num at h; exact h
  have h10 : sigmaStar 49141 = 49612 := by
    have h := sigmaStar_step (p := 157) (k := 1) (m := 313) (N := 49141) (by norm_num) one_ne_zero
      (by norm_num) (by norm_num) (by norm_num) h11
    norm_num at h; exact h
  have h9 : sigmaStar 5356369 = 5457320 := by
    have h := sigmaStar_step (p := 109) (k := 1) (m := 49141) (N := 5356369) (by norm_num)
      one_ne_zero (by norm_num) (by norm_num) (by norm_num) h10
    norm_num at h; exact h
  have h8 : sigmaStar 423153151 = 436585600 := by
    have h := sigmaStar_step (p := 79) (k := 1) (m := 5356369) (N := 423153151) (by norm_num)
      one_ne_zero (by norm_num) (by norm_num) (by norm_num) h9
    norm_num at h; exact h
  have h7 : sigmaStar 15656666587 = 16590252800 := by
    have h := sigmaStar_step (p := 37) (k := 1) (m := 423153151) (N := 15656666587) (by norm_num)
      one_ne_zero (by norm_num) (by norm_num) (by norm_num) h8
    norm_num at h; exact h
  have h6 : sigmaStar 297476665153 = 331805056000 := by
    have h := sigmaStar_step (p := 19) (k := 1) (m := 15656666587) (N := 297476665153) (by norm_num)
      one_ne_zero (by norm_num) (by norm_num) (by norm_num) h7
    norm_num at h; exact h
  have h5 : sigmaStar 3867196646989 = 4645270784000 := by
    have h := sigmaStar_step (p := 13) (k := 1) (m := 297476665153) (N := 3867196646989)
      (by norm_num) one_ne_zero (by norm_num) (by norm_num) (by norm_num) h6
    norm_num at h; exact h
  have h4 : sigmaStar 42539163116879 = 55743249408000 := by
    have h := sigmaStar_step (p := 11) (k := 1) (m := 3867196646989) (N := 42539163116879)
      (by norm_num) one_ne_zero (by norm_num) (by norm_num) (by norm_num) h5
    norm_num at h; exact h
  have h3 : sigmaStar 297774141818153 = 445945995264000 := by
    have h := sigmaStar_step (p := 7) (k := 1) (m := 42539163116879) (N := 297774141818153)
      (by norm_num) one_ne_zero (by norm_num) (by norm_num) (by norm_num) h4
    norm_num at h; exact h
  have h2 : sigmaStar 186108838636345625 = 279162193035264000 := by
    have h := sigmaStar_step (p := 5) (k := 4) (m := 297774141818153) (N := 186108838636345625)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h3
    norm_num at h; exact h
  have h1 : sigmaStar 558326515909036875 = 1116648772141056000 := by
    have h := sigmaStar_step (p := 3) (k := 1) (m := 186108838636345625) (N := 558326515909036875)
      (by norm_num) one_ne_zero (by norm_num) (by norm_num) (by norm_num) h2
    norm_num at h; exact h
  have h0 := sigmaStar_step (p := 2) (k := 18) (m := 558326515909036875)
    (N := 146361946186458562560000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h1
  norm_num at h0; exact h0

/-- All five known unitary perfect numbers really are unitary perfect. -/
theorem known_isUnitaryPerfect : ∀ n ∈ known, IsUnitaryPerfect n := by
  intro n hn
  simp only [known, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by rw [sigmaStar_6]⟩
  · exact ⟨by norm_num, by rw [sigmaStar_60]⟩
  · exact ⟨by norm_num, by rw [sigmaStar_90]⟩
  · exact ⟨by norm_num, by rw [sigmaStar_87360]⟩
  · exact ⟨by norm_num, by rw [sigmaStar_fifth]⟩

end KnownExamples

section Structure

variable {n : ℕ}

lemma IsUnitaryPerfect.one_lt (h : IsUnitaryPerfect n) : 1 < n := by
  rcases h with ⟨hpos, heq⟩
  rcases Nat.lt_or_ge 1 n with h | h
  · exact h
  · interval_cases n
    · simp [sigmaStar_one] at heq

/-- If `n > 1` and every prime factor of `n` equals `p`, then `n` is a power of `p`. -/
lemma eq_pow_of_unique_primeFactor {p : ℕ} (hn : 1 < n)
    (hall : ∀ q ∈ n.primeFactors, q = p) : n = p ^ n.factorization p := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.2 hn
  have hp : p ∈ n.primeFactors := (hall q hq) ▸ hq
  have hcard : n.primeFactors = {p} := Finset.eq_singleton_iff_unique_mem.2 ⟨hp, hall⟩
  have hh := prod_primeFactors_pow hn0
  rw [hcard, Finset.prod_singleton] at hh
  exact hh.symm

/-- Every unitary perfect number has an odd prime factor; in particular it is not a power
of two. -/
theorem exists_odd_prime_factor (h : IsUnitaryPerfect n) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ n := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ q ∈ n.primeFactors, q = 2 := by
    intro q hq
    by_contra hne
    exact hcon q (Nat.prime_of_mem_primeFactors hq) hne (Nat.dvd_of_mem_primeFactors hq)
  have hn2 : n = 2 ^ n.factorization 2 := eq_pow_of_unique_primeFactor h.one_lt hall
  have hk : n.factorization 2 ≠ 0 := by
    intro hk0
    rw [hk0, pow_zero] at hn2
    exact absurd hn2 h.one_lt.ne'
  have h2 := h.2
  rw [hn2, sigmaStar_prime_pow Nat.prime_two hk] at h2
  have h1 : 1 < 2 ^ n.factorization 2 := Nat.one_lt_two_pow_iff.mpr hk
  generalize (2 : ℕ) ^ n.factorization 2 = a at h2 h1
  omega

/-- There are no odd unitary perfect numbers: every unitary perfect number is even. -/
theorem even_of_isUnitaryPerfect (h : IsUnitaryPerfect n) : Even n := by
  classical
  by_contra hodd
  have hn0 : n ≠ 0 := h.1.ne'
  have hn2 : ¬ (2 ∣ n) := fun hd => hodd (even_iff_two_dvd.mpr hd)
  -- every prime factor of `n` is odd, hence every factor `p ^ v_p(n) + 1` of `σ*(n)` is even
  have hfac : ∀ p ∈ n.primeFactors, 2 ∣ (p ^ n.factorization p + 1) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpne : p ≠ 2 := by
      rintro rfl
      exact hn2 (Nat.dvd_of_mem_primeFactors hp)
    have hpodd : ¬ (2 ∣ p) := fun hd =>
      hpne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1 hd).symm
    have hnd : ¬ (2 ∣ p ^ n.factorization p) := fun hd =>
      hpodd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd)
    omega
  have hpow : 2 ^ n.primeFactors.card ∣ sigmaStar n := by
    rw [sigmaStar_eq_prod_primeFactors hn0, ← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ hfac
  -- so `n` cannot have two distinct prime factors, else `4 ∣ 2n`
  have hcard1 : n.primeFactors.card ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h4 : (4 : ℕ) ∣ sigmaStar n := dvd_trans (by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ n.primeFactors.card := pow_dvd_pow 2 hc) hpow
    rw [h.2] at h4
    obtain ⟨c, hc'⟩ := h4
    exact hn2 ⟨c, by omega⟩
  -- hence `n = p ^ k` with `p ^ k + 1 = 2 p ^ k`, which is impossible
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 h.one_lt
  have hall : ∀ q ∈ n.primeFactors, q = p := by
    intro q hq
    by_contra hqp
    have : 2 ≤ n.primeFactors.card := Finset.one_lt_card.2 ⟨q, hq, p, hp, hqp⟩
    omega
  have hnp : n = p ^ n.factorization p := eq_pow_of_unique_primeFactor h.one_lt hall
  have hcard : n.primeFactors = {p} := Finset.eq_singleton_iff_unique_mem.2 ⟨hp, hall⟩
  have h2 := h.2
  rw [sigmaStar_eq_prod_primeFactors hn0, hcard, Finset.prod_singleton, ← hnp] at h2
  have := h.one_lt
  omega

lemma two_mem_primeFactors (h : IsUnitaryPerfect n) : 2 ∈ n.primeFactors :=
  Nat.mem_primeFactors.2 ⟨Nat.prime_two, (even_of_isUnitaryPerfect h).two_dvd, h.1.ne'⟩

/-- A unitary perfect number has at least two distinct prime factors. -/
theorem two_le_card_primeFactors (h : IsUnitaryPerfect n) : 2 ≤ n.primeFactors.card := by
  obtain ⟨p, hp, hp2, hpn⟩ := exists_odd_prime_factor h
  exact Finset.one_lt_card.2 ⟨2, two_mem_primeFactors h, p,
    Nat.mem_primeFactors.2 ⟨hp, hpn, h.1.ne'⟩, Ne.symm hp2⟩

/-- The arithmetic heart of the two-prime case: `(x+1)(y+1) = 2xy` with `x ≥ 2`, `y ≥ 3`
forces `x = 2` and `y = 3`. -/
lemma two_mul_three_of_prod_eq (x y : ℕ) (hx : 2 ≤ x) (hy : 3 ≤ y)
    (h : (x + 1) * (y + 1) = 2 * (x * y)) : x = 2 ∧ y = 3 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = u + 1 := ⟨x - 1, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, y = v + 1 := ⟨y - 1, by omega⟩
  have huv : u * v = 2 := by nlinarith [h]
  have hu2 : u ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨v, huv.symm⟩
  interval_cases u <;> omega

/-- A unitary perfect number with exactly two distinct prime factors is `6`. -/
theorem eq_six_of_card_primeFactors_eq_two (h : IsUnitaryPerfect n)
    (hcard : n.primeFactors.card = 2) : n = 6 := by
  have hn0 : n ≠ 0 := h.1.ne'
  have h2 : 2 ∈ n.primeFactors := two_mem_primeFactors h
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1 hcard
  obtain ⟨p, hp2, hpf⟩ : ∃ p, p ≠ 2 ∧ n.primeFactors = {2, p} := by
    rw [hs] at h2
    rcases Finset.mem_insert.1 h2 with rfl | hb
    · exact ⟨b, fun hb => hab hb.symm, hs⟩
    · rw [Finset.mem_singleton] at hb
      subst hb
      exact ⟨a, fun ha => hab ha, by rw [hs, Finset.pair_comm]⟩
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hpf]; simp)
  have hne : (2 : ℕ) ≠ p := Ne.symm hp2
  have hprod : n = 2 ^ n.factorization 2 * p ^ n.factorization p := by
    have hh := prod_primeFactors_pow hn0
    rw [hpf, Finset.prod_pair hne] at hh
    exact hh.symm
  have hsig : sigmaStar n = (2 ^ n.factorization 2 + 1) * (p ^ n.factorization p + 1) := by
    rw [sigmaStar_eq_prod_primeFactors hn0, hpf, Finset.prod_pair hne]
  have hA : n.factorization 2 ≠ 0 := by
    have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 (Nat.dvd_of_mem_primeFactors h2)
    omega
  have hB : n.factorization p ≠ 0 := by
    have := Nat.Prime.factorization_pos_of_dvd hp hn0
      (Nat.dvd_of_mem_primeFactors (by rw [hpf]; simp))
    omega
  have hx : 2 ≤ 2 ^ n.factorization 2 := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hy : 3 ≤ p ^ n.factorization p := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    calc (3 : ℕ) ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n.factorization p := Nat.pow_le_pow_right (by omega) (by omega)
  have key : (2 ^ n.factorization 2 + 1) * (p ^ n.factorization p + 1)
      = 2 * (2 ^ n.factorization 2 * p ^ n.factorization p) := by
    rw [← hsig, h.2, ← hprod]
  obtain ⟨hx2, hy3⟩ := two_mul_three_of_prod_eq _ _ hx hy key
  rw [hprod, hx2, hy3]

end Structure

/-!
## The target statement

`SixthUnitaryPerfectExists` is a conditional reduction: the existence of *any* unitary
perfect number outside the known list yields a "sixth" unitary perfect number carrying all
the structural constraints proved above.  The unconditional existence statement is an open
problem and is therefore not asserted.
-/

/-- **Sixth unitary perfect number (conditional).**  If some unitary perfect number is not
one of the five known ones, then there is a sixth unitary perfect number, and it is
necessarily even, greater than `6`, divisible by an odd prime, and has at least three
distinct prime factors. -/
theorem SixthUnitaryPerfectExists
    (h : ∃ n, IsUnitaryPerfect n ∧ n ∉ known) :
    ∃ n, IsUnitaryPerfect n ∧ n ∉ known ∧ Even n ∧ 6 < n ∧ 3 ≤ n.primeFactors.card ∧
      ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ n := by
  obtain ⟨n, hn, hnk⟩ := h
  obtain ⟨p, hp, hp2, hpn⟩ := exists_odd_prime_factor hn
  have heven : Even n := even_of_isUnitaryPerfect hn
  have hn6 : n ≠ 6 := by rintro rfl; exact hnk (by simp [known])
  have hcard : 3 ≤ n.primeFactors.card := by
    have h2 := two_le_card_primeFactors hn
    rcases Nat.lt_or_ge n.primeFactors.card 3 with hlt | hge
    · exact absurd (eq_six_of_card_primeFactors_eq_two hn (by omega)) hn6
    · exact hge
  refine ⟨n, hn, hnk, heven, ?_, hcard, p, hp, hp2, hpn⟩
  -- `n` is divisible by `2p ≥ 6`, and `n ≠ 6` because `6` belongs to the known list
  have h2 : 2 ∣ n := heven.two_dvd
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have h2p : 2 * p ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 hpn
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hge : 6 ≤ n := le_trans (by omega) (Nat.le_of_dvd hn.1 h2p)
  rcases Nat.lt_or_ge 6 n with hlt | hle
  · exact hlt
  · exact absurd (by omega : n = 6) hn6

end UnitaryPerfect
end Brockian

