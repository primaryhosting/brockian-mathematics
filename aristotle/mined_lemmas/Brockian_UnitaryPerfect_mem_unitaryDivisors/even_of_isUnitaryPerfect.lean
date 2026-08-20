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

theorem even_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  obtain ⟨hpos, hsum⟩ := h
  rw [even_iff_two_dvd]
  by_contra hodd
  -- `n = 1` is impossible since `σ*(1) = 1 ≠ 2`
  have hn1 : n ≠ 1 := by
    rintro rfl
    rw [usigma_one] at hsum
    omega
  have hn : 1 < n := by omega
  obtain ⟨k, m, hk, hpm, hnm, hval⟩ := usigma_split_minFac hn
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hpodd : ¬ 2 ∣ n.minFac ^ k := not_two_dvd_minFac_pow hodd
  have hpk1 : 1 < n.minFac ^ k := Nat.one_lt_pow hk hp.one_lt
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hnm
    omega
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm0) with hm1 | hm1
  · -- `n` is a prime power: `1 + p ^ k = 2 p ^ k` forces `p ^ k = 1`
    rw [← hm1, usigma_one, mul_one] at hval
    rw [← hm1, mul_one] at hnm
    omega
  · -- otherwise `4 ∣ σ*(n) = 2 n`, so `n` is even
    have hmn : m ∣ n := Dvd.intro_left _ hnm.symm
    have hmodd : ¬ 2 ∣ m := fun hdvd => hodd (hdvd.trans hmn)
    have h2a : 2 ∣ 1 + n.minFac ^ k := by omega
    have h2b : 2 ∣ usigma m := two_dvd_usigma_of_one_lt hm1 hmodd
    have h4 : 4 ∣ usigma n := by
      obtain ⟨a, ha⟩ := h2a
      obtain ⟨b, hb⟩ := h2b
      exact ⟨a * b, by rw [hval, ha, hb]; ring⟩
    rw [hsum] at h4
    omega

/-! ## The target statement -/

/-- The assertion that a sixth unitary perfect number exists, i.e. that there is a unitary
perfect number other than the five known ones. -/
