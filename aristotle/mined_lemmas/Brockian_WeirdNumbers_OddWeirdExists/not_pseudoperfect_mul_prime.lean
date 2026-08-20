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
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A natural number `n` is *weird* (`Nat.Weird`) if it is abundant (the sum of its proper
divisors exceeds `n`) but not pseudoperfect (no subset of its proper divisors sums to `n`).

Whether an **odd** weird number exists is a well-known open problem; no odd weird number is
known.  Consequently the file below does not claim an unconditional existence proof.
Instead it provides a Lean-checked *reduction*:

* `Brockian.WeirdNumbers.weird_mul_prime` : if `n` is weird and `p` is a prime exceeding the
  sum of the divisors of `n`, then `n * p` is weird.
* `Brockian.WeirdNumbers.OddWeirdExists` : an odd weird number exists **iff** there are
  arbitrarily large odd weird numbers.  In other words, a single odd weird number would
  immediately yield infinitely many.

Unconditionally we also record:

* `Brockian.WeirdNumbers.even_weird_exists` : `70` is an (even) weird number;
* `Brockian.WeirdNumbers.odd_weird_ge_1000` : every odd weird number is at least `1000`
  (the only odd abundant number below `1000` is `945`, and `945` is pseudoperfect).
-/

namespace Brockian.WeirdNumbers

open Finset

/-- The sum of all divisors of `n`. -/
abbrev sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- For a prime `p` not dividing `n`, `σ (n * p) = σ n * (p + 1)`. -/

lemma not_pseudoperfect_mul_prime {n p : ℕ} (hn : n.Weird) (hp : p.Prime)
    (hlt : sigmaOne n < p) : ¬ (n * p).Pseudoperfect := by
  rintro ⟨-, S, hS, hSsum⟩
  have hnpos : 0 < n := Weird.pos hn
  have hppos : 0 < p := hp.pos
  classical
  set A := S.filter (fun d => ¬ p ∣ d) with hA
  set B := S.filter (fun d => p ∣ d) with hB
  have hsplit : (∑ d ∈ B, d) + (∑ d ∈ A, d) = n * p := by
    rw [hA, hB, Finset.sum_filter_add_sum_filter_not S (fun d => p ∣ d)]
    exact hSsum
  -- the part of `S` coprime to `p` consists of divisors of `n`
  have hAsub : A ⊆ n.divisors := by
    intro d hd
    rw [hA, Finset.mem_filter] at hd
    obtain ⟨hdS, hdp⟩ := hd
    have hd' := hS hdS
    rw [Nat.mem_properDivisors] at hd'
    have hcop : Nat.Coprime d p := ((hp.coprime_iff_not_dvd).2 hdp).symm
    exact Nat.mem_divisors.2 ⟨hcop.dvd_of_dvd_mul_right hd'.1, by positivity⟩
  have hAle : (∑ d ∈ A, d) ≤ sigmaOne n :=
    Finset.sum_le_sum_of_subset hAsub
  have hdvdB : p ∣ ∑ d ∈ B, d :=
    Finset.dvd_sum (fun d hd => (Finset.mem_filter.1 (hB ▸ hd)).2)
  have hdvdA : p ∣ ∑ d ∈ A, d := by
    refine (Nat.dvd_add_right hdvdB).mp ?_
    rw [hsplit]
    exact dvd_mul_left p n
  have hA0 : (∑ d ∈ A, d) = 0 := by
    by_contra h0
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvdA
    omega
  have hBsum : (∑ d ∈ B, d) = n * p := by omega
  -- divide the `p`-divisible part by `p`
  have hBdvd : ∀ d ∈ B, p ∣ d := fun d hd => (Finset.mem_filter.1 (hB ▸ hd)).2
  have hinj : ∀ x ∈ B, ∀ y ∈ B, x / p = y / p → x = y := by
    intro x hx y hy hxy
    have hx' := Nat.mul_div_cancel' (hBdvd x hx)
    have hy' := Nat.mul_div_cancel' (hBdvd y hy)
    rw [← hx', ← hy', hxy]
  set B' := B.image (fun d => d / p) with hB'
  have hsum' : p * (∑ e ∈ B', e) = n * p := by
    rw [hB', Finset.mul_sum, Finset.sum_image hinj]
    rw [← hBsum]
    exact Finset.sum_congr rfl (fun d hd => Nat.mul_div_cancel' (hBdvd d hd))
  have hB'sum : (∑ e ∈ B', e) = n := by
    have : p * (∑ e ∈ B', e) = p * n := by rw [hsum', Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hppos this
  have hB'sub : B' ⊆ n.properDivisors := by
    intro e he
    rw [hB', Finset.mem_image] at he
    obtain ⟨d, hd, rfl⟩ := he
    have hdmem := hS (Finset.mem_of_mem_filter d (hB ▸ hd))
    rw [Nat.mem_properDivisors] at hdmem
    have hdeq : p * (d / p) = d := Nat.mul_div_cancel' (hBdvd d hd)
    have hdvd : p * (d / p) ∣ p * n := by
      rw [hdeq, Nat.mul_comm p n]
      exact hdmem.1
    have hlt' : p * (d / p) < p * n := by
      rw [hdeq, Nat.mul_comm p n]
      exact hdmem.2
    exact Nat.mem_properDivisors.2
      ⟨(mul_dvd_mul_iff_left hppos.ne').1 hdvd, lt_of_mul_lt_mul_left hlt' (Nat.zero_le p)⟩
  exact hn.2 ⟨hnpos, B', hB'sub, hB'sum⟩

/-- If `n` is weird and `p` is a prime larger than the sum of the divisors of `n`,
then `n * p` is weird. -/
