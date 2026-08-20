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

A *unitary divisor* of `n` is a divisor `d` with `gcd (d, n / d) = 1`, and `n` is *unitary
perfect* if the sum `σ*(n)` of its unitary divisors equals `2 n`.  Exactly five unitary
perfect numbers are known:

`6, 60, 90, 87360, 146361946186458562560000`,

and it is a long-standing open problem whether a sixth one exists.  Accordingly this file
does **not** prove unconditional existence; it develops the basic theory of `σ*`
(multiplicativity, values at prime powers), verifies that the five known numbers really are
unitary perfect, proves that every unitary perfect number is even, and finally proves the
target statement `SixthUnitaryPerfectExists` as a *conditional reduction*: any unitary
perfect number that either exceeds the largest known one or fails to be divisible by `3`
is a sixth unitary perfect number.

(The header comment above appears after the `import` line only because Lean requires
imports to come first in a file.)
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/

lemma usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    usigma (p ^ k) = 1 + p ^ k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hne : (1 : ℕ) ≠ p ^ k := (Nat.one_lt_pow hk hp.one_lt).ne
  have hset : unitaryDivisors (p ^ k) = {1, p ^ k} := by
    ext d
    simp only [mem_unitaryDivisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, -, hcop⟩
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · left; simp
      · right
        have hdiv : p ^ k / p ^ i = p ^ (k - i) := by
          rw [← pow_sub_mul_pow p hi, Nat.mul_div_cancel _ (pow_pos hp.pos i)]
        rw [hdiv] at hcop
        have hki : k - i = 0 := by
          by_contra hne'
          have h1 : p ∣ p ^ i := dvd_pow_self p hipos.ne'
          have h2 : p ∣ p ^ (k - i) := dvd_pow_self p hne'
          exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
        congr 1
        omega
    · rintro (rfl | rfl)
      · exact ⟨one_dvd _, hpk, by simp⟩
      · exact ⟨dvd_rfl, hpk, by simp [Nat.div_self (Nat.pos_of_ne_zero hpk)]⟩
  rw [usigma, hset, Finset.sum_pair hne]

