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

theorem usigma_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    usigma (m * n) = usigma m * usigma n := by
  unfold usigma
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine (Finset.sum_nbij' (i := fun x => x.1 * x.2) (j := fun d => (Nat.gcd d m, Nat.gcd d n))
    ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product] at hab
    obtain ⟨ha, hb⟩ := hab
    rw [mem_unitaryDivisors] at ha hb ⊢
    obtain ⟨ha1, -, ha2⟩ := ha
    obtain ⟨hb1, -, hb2⟩ := hb
    have hdiv : m * n / (a * b) = (m / a) * (n / b) := Nat.mul_div_mul_comm ha1 hb1
    refine ⟨mul_dvd_mul ha1 hb1, by positivity, ?_⟩
    rw [hdiv]
    have ham : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left ha1 h
    have hbn : Nat.Coprime b m := Nat.Coprime.coprime_dvd_left hb1 h.symm
    exact Nat.Coprime.mul_left
      (Nat.Coprime.mul_right ha2 (ham.coprime_dvd_right (Nat.div_dvd_of_dvd hb1)))
      (Nat.Coprime.mul_right (hbn.coprime_dvd_right (Nat.div_dvd_of_dvd ha1)) hb2)
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hd1, -, hd2⟩ := hd
    have hgm : Nat.gcd d m ∣ m := Nat.gcd_dvd_right d m
    have hgn : Nat.gcd d n ∣ n := Nat.gcd_dvd_right d n
    have hsplit : Nat.gcd d m * Nat.gcd d n = d := by
      rw [← h.gcd_mul d, Nat.gcd_eq_left hd1]
    have hdiv : m * n / d = (m / Nat.gcd d m) * (n / Nat.gcd d n) := by
      calc m * n / d = m * n / (Nat.gcd d m * Nat.gcd d n) := by rw [hsplit]
        _ = (m / Nat.gcd d m) * (n / Nat.gcd d n) := Nat.mul_div_mul_comm hgm hgn
    rw [hdiv] at hd2
    simp only [Finset.mem_product, mem_unitaryDivisors]
    exact ⟨⟨hgm, hm, (hd2.coprime_dvd_left (Nat.gcd_dvd_left d m)).coprime_dvd_right
        (Dvd.intro _ rfl)⟩,
      ⟨hgn, hn, (hd2.coprime_dvd_left (Nat.gcd_dvd_left d n)).coprime_dvd_right
        (Dvd.intro_left _ rfl)⟩⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_product, mem_unitaryDivisors] at hab
    obtain ⟨⟨ha1, -, -⟩, ⟨hb1, -, -⟩⟩ := hab
    have ham : Nat.Coprime a n := Nat.Coprime.coprime_dvd_left ha1 h
    have hbn : Nat.Coprime b m := Nat.Coprime.coprime_dvd_left hb1 h.symm
    have h1 : Nat.gcd (a * b) m = a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a hbn, Nat.gcd_eq_left ha1]
    have h2 : Nat.gcd (a * b) n = b := by
      rw [Nat.Coprime.gcd_mul_left_cancel b ham, Nat.gcd_eq_left hb1]
    simp [h1, h2]
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    show Nat.gcd d m * Nat.gcd d n = d
    rw [← h.gcd_mul d, Nat.gcd_eq_left hd.1]
  · rintro ⟨a, b⟩ _; rfl

/-- Multiplicativity of `σ*` without positivity assumptions. -/
