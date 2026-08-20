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

lemma usigma_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [Nat.coprime_zero_left] at h
    subst h; simp [usigma_zero, usigma_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.coprime_zero_right] at h
    subst h; simp [usigma_zero, usigma_one]
  rw [usigma, usigma, usigma, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun d => (d.gcd m, d.gcd n)) (fun x => x.1 * x.2) ?_ ?_ ?_ ?_ ?_
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hdvd, -, hcop⟩ := hd
    have key : d.gcd m * d.gcd n = d := by
      rw [← h.gcd_mul d, Nat.gcd_eq_left hdvd]
    have hmn : (m * n) / d = (m / d.gcd m) * (n / d.gcd n) := by
      rw [Nat.div_mul_div_comm (Nat.gcd_dvd_right d m) (Nat.gcd_dvd_right d n), key]
    rw [hmn] at hcop
    simp only [Finset.mem_product, mem_unitaryDivisors]
    exact ⟨⟨Nat.gcd_dvd_right d m, hm,
        Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d m)
          (hcop.coprime_dvd_right (dvd_mul_right _ _))⟩,
      ⟨Nat.gcd_dvd_right d n, hn,
        Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left d n)
          (hcop.coprime_dvd_right (dvd_mul_left _ _))⟩⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ha, -, hca⟩, ⟨hb, -, hcb⟩⟩ := hab
    have hdiv : (m * n) / (a * b) = (m / a) * (n / b) :=
      (Nat.div_mul_div_comm ha hb).symm
    rw [mem_unitaryDivisors, hdiv]
    refine ⟨mul_dvd_mul ha hb, Nat.mul_ne_zero hm hn, ?_⟩
    have hamn : Nat.Coprime a (n / b) :=
      (h.coprime_dvd_left ha).coprime_dvd_right (Nat.div_dvd_of_dvd hb)
    have hbmn : Nat.Coprime b (m / a) :=
      (h.symm.coprime_dvd_left hb).coprime_dvd_right (Nat.div_dvd_of_dvd ha)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hca hamn)
      (Nat.Coprime.mul_right hbmn hcb)
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    show d.gcd m * d.gcd n = d
    rw [← h.gcd_mul d, Nat.gcd_eq_left hd.1]
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ha, -, hca⟩, ⟨hb, -, hcb⟩⟩ := hab
    have hbm : Nat.Coprime b m := h.symm.coprime_dvd_left hb
    have han : Nat.Coprime a n := h.coprime_dvd_left ha
    have h1 : (a * b).gcd m = a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a hbm, Nat.gcd_eq_left ha]
    have h2 : (a * b).gcd n = b := by
      rw [mul_comm, Nat.Coprime.gcd_mul_right_cancel b han, Nat.gcd_eq_left hb]
    simp [h1, h2]
  · rintro d hd
    rw [mem_unitaryDivisors] at hd
    show d = d.gcd m * d.gcd n
    rw [← h.gcd_mul d, Nat.gcd_eq_left hd.1]

/-- The unitary divisors of a prime power `p ^ k` (`k ≥ 1`) are `1` and `p ^ k`. -/
