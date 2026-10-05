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

theorem sixthUnitaryPerfect_criterion :
    (∃ n : ℕ, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect) ↔
      (∃ a m : ℕ, 1 ≤ a ∧ Odd m ∧ (1 + 2 ^ a) * usigma m = 2 ^ (a + 1) * m ∧
        2 ^ a * m ∉ knownUnitaryPerfect) := by
  constructor
  · rintro ⟨n, hup, hnot⟩
    have hn : n ≠ 0 := hup.1.ne'
    have heven : 2 ∣ n := (even_of_isUnitaryPerfect hup).two_dvd
    have ha : 1 ≤ n.factorization 2 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn heven
    have hsplit : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n 2
    have hmodd : Odd (n / 2 ^ n.factorization 2) := by
      have h := Nat.not_dvd_ordCompl Nat.prime_two hn
      rw [Nat.odd_iff]
      omega
    exact ⟨n.factorization 2, n / 2 ^ n.factorization 2, ha, hmodd,
      (isUnitaryPerfect_iff_odd_part ha hmodd).1 (by rwa [hsplit]), by rwa [hsplit]⟩
  · rintro ⟨a, m, ha, hm, heq, hnot⟩
    exact ⟨2 ^ a * m, (isUnitaryPerfect_iff_odd_part ha hm).2 heq, hnot⟩

end Brockian.UnitaryPerfect

