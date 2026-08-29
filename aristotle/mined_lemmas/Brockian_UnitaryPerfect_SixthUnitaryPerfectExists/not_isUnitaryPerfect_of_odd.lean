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

A *unitary divisor* of `n` is a divisor `d` with `gcd d (n / d) = 1`, and `n` is *unitary
perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.  Exactly five unitary
perfect numbers are known:

`6`, `60`, `90`, `87360`, `146361946186458562560000`,

and whether a sixth one exists is an open problem.  This file develops the basic theory
(`σ*` is multiplicative, `σ*(p^a) = 1 + p^a`, the factorization formula), verifies the five
known examples, proves that every unitary perfect number is even, and reduces the existence
of a sixth unitary perfect number to an explicit arithmetic criterion on the odd part.
-/

open Finset

namespace Brockian.UnitaryPerfect

/-- The unitary divisors of `n`: divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem not_isUnitaryPerfect_of_odd {n : ℕ} (hodd : Odd n) : ¬ IsUnitaryPerfect n := by
  rintro ⟨hpos, heq⟩
  have hn : n ≠ 0 := hpos.ne'
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  have h2 : ¬ (2 ∣ n) := by omega
  have hprod := usigma_eq_prod_primeFactors hn
  have hdvd : 2 ^ n.primeFactors.card ∣ usigma n := by
    rw [hprod, ← Finset.prod_const]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpodd : Odd p := by
      rcases Nat.even_or_odd p with he | ho
      · exact absurd (dvd_trans he.two_dvd hpdvd) h2
      · exact ho
    exact (Odd.add_odd odd_one hpodd.pow).two_dvd
  rcases lt_trichotomy n.primeFactors.card 1 with hc | hc | hc
  · have hcard : n.primeFactors.card = 0 := by omega
    have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard
    have hn1 : n = 1 := by
      rcases Nat.primeFactors_eq_empty.mp hempty with h | h
      · exact absurd h hn
      · exact h
    rw [hn1, usigma_one] at heq
    omega
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hprod2 : usigma n = 1 + n := by
      rw [hprod, hp, Finset.prod_singleton]
      have hpow : ∏ q ∈ n.primeFactors, q ^ n.factorization q = n :=
        prod_pow_factorization_self hn
      rw [hp, Finset.prod_singleton] at hpow
      rw [hpow]
    rw [hprod2] at heq
    have hn1 : n = 1 := by omega
    have hempty : n.primeFactors = ∅ := by rw [hn1]; simp
    rw [hempty] at hp
    simp at hp
  · have h4 : (4 : ℕ) ∣ usigma n :=
      dvd_trans (by norm_num) (dvd_trans (pow_dvd_pow 2 hc) hdvd)
    rw [heq] at h4
    omega

/-- Every unitary perfect number is even. -/
