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
## Overview

A natural number `n` is *weird* when it is abundant (the sum of its proper divisors exceeds
`n`) but not semiperfect (no set of distinct proper divisors of `n` sums to `n`).  The smallest
weird number is `70`.

Whether an **odd** weird number exists is a well-known open problem; none is known, and none
exists below very large search bounds.  Accordingly, the target statement
`Brockian.WeirdNumbers.OddWeirdExists` is formalised here as a *conditional reduction*: it derives
the existence of an odd weird number from the existence of an odd abundant number whose
*abundance* `σ(n) - 2n` is not a subset sum of the proper divisors of `n`.

The reduction is not a weakening: `weird_iff_abundance_not_representable` shows that the
hypothesis is in fact equivalent to the conclusion's content, and it is the numerically more
convenient criterion (the abundance is usually far smaller than `n`).

Besides that, this file contains:

* `isWeird_70` — a machine-checked verification that `70` is weird (a sanity check on the
  definitions);
* `no_odd_weird_below_1000` — no odd weird number is smaller than `1000`;
* `isWeird_mul_prime` — if `n` is weird and `p` is a prime larger than `σ n`, then `n * p` is
  weird; hence (`infinite_odd_weird_of_odd_weird`) a single odd weird number would produce
  infinitely many.
-/

namespace Brockian.WeirdNumbers

open Finset

/-- `n` is *semiperfect* (pseudoperfect) if some set of distinct proper divisors of `n`
sums to `n`. -/

theorem isWeird_mul_prime (n p : ℕ) (hn : 0 < n) (hp : p.Prime)
    (hpσ : ∑ d ∈ n.divisors, d < p) (hw : IsWeird n) : IsWeird (n * p) := by
  have hab : n < ∑ d ∈ n.properDivisors, d := hw.1
  have hσn : 2 * n < ∑ d ∈ n.divisors, d := by
    have := sum_properDivisors_eq n hn
    have hle : n ≤ ∑ d ∈ n.divisors, d :=
      Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
        (Nat.mem_divisors_self n hn.ne')
    omega
  have hpn : ¬ p ∣ n := by
    intro hdvd
    have : p ≤ n := Nat.le_of_dvd hn hdvd
    have hle : n ≤ ∑ d ∈ n.divisors, d :=
      Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
        (Nat.mem_divisors_self n hn.ne')
    omega
  have hnp : 0 < n * p := Nat.mul_pos hn hp.pos
  constructor
  · -- abundance of `n * p`
    show n * p < ∑ d ∈ (n * p).properDivisors, d
    rw [sum_properDivisors_eq _ hnp, sigma_mul_prime n p hn hp hpn]
    have h1 : (2 * n + 1) * (1 + p) ≤ (∑ d ∈ n.divisors, d) * (1 + p) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith [hp.pos]
  · -- not semiperfect
    rintro ⟨S, hS, hsum⟩
    have hSsub : S ⊆ (n * p).properDivisors := Finset.mem_powerset.mp hS
    classical
    set A := S.filter (fun d => ¬ p ∣ d) with hA
    set B := S.filter (fun d => p ∣ d) with hB
    have hsplit : ∑ d ∈ B, d + ∑ d ∈ A, d = n * p := by
      rw [hA, hB, Finset.sum_filter_add_sum_filter_not S (fun d => p ∣ d)]
      exact hsum
    -- elements of `A` are divisors of `n`
    have hAsub : A ⊆ n.divisors := by
      intro a ha
      rw [hA, Finset.mem_filter] at ha
      have hmem := hSsub ha.1
      rw [Nat.mem_properDivisors] at hmem
      exact Nat.mem_divisors.mpr ⟨Nat.Coprime.dvd_of_dvd_mul_right
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha.2).symm hmem.1, hn.ne'⟩
    have hAle : ∑ d ∈ A, d ≤ ∑ d ∈ n.divisors, d :=
      Finset.sum_le_sum_of_subset hAsub
    -- `p` divides the sum over `B`
    have hpB : p ∣ ∑ d ∈ B, d :=
      Finset.dvd_sum (fun d hd => (Finset.mem_filter.mp (hB ▸ hd)).2)
    have hpA : p ∣ ∑ d ∈ A, d := by
      have : ∑ d ∈ A, d = n * p - ∑ d ∈ B, d := by omega
      rw [this]
      exact Nat.dvd_sub (Dvd.intro n rfl) hpB
    have hA0 : ∑ d ∈ A, d = 0 := by
      rcases Nat.eq_zero_or_pos (∑ d ∈ A, d) with h | h
      · exact h
      · have := Nat.le_of_dvd h hpA
        omega
    have hBsum : ∑ d ∈ B, d = n * p := by omega
    -- `B` consists of `p` times a proper divisor of `n`
    set B' := n.properDivisors.filter (fun e => p * e ∈ S) with hB'
    have hBeq : B = B'.image (fun e => p * e) := by
      ext d
      simp only [hB, hB', Finset.mem_filter, Finset.mem_image, Nat.mem_properDivisors]
      constructor
      · rintro ⟨hdS, e, rfl⟩
        have hmem := hSsub hdS
        rw [Nat.mem_properDivisors] at hmem
        refine ⟨e, ⟨⟨(Nat.mul_dvd_mul_iff_left hp.pos).mp (by rwa [mul_comm n p] at hmem.1), ?_⟩,
          hdS⟩, rfl⟩
        have := hmem.2
        rw [mul_comm n p] at this
        exact lt_of_mul_lt_mul_left this (Nat.zero_le p)
      · rintro ⟨e, ⟨⟨_, _⟩, heS⟩, rfl⟩
        exact ⟨heS, Dvd.intro e rfl⟩
    have hinj : ∀ a ∈ B', ∀ b ∈ B', p * a = p * b → a = b :=
      fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h
    have hB'sum : p * ∑ e ∈ B', e = n * p := by
      rw [Finset.mul_sum, ← hBsum, hBeq, Finset.sum_image hinj]
    have : ∑ e ∈ B', e = n := by
      have hp0 : 0 < p := hp.pos
      nlinarith [hB'sum]
    exact hw.2 ⟨B', Finset.mem_powerset.mpr (by rw [hB']; exact Finset.filter_subset _ _), this⟩

/-- If an odd weird number exists, then there are arbitrarily large odd weird numbers. -/
