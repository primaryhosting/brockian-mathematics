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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure

A *Zumkeller number* is a positive integer whose divisors can be split into two sets with
equal sums.  Here we prove that an odd Zumkeller number must have at least three distinct
prime factors.

The argument: a Zumkeller number is perfect or abundant (`σ(n) ≥ 2n`), while an odd number
with at most two distinct prime factors `p < q` satisfies
`σ(n)/n < p/(p-1) · q/(q-1) ≤ (3/2)(5/4) < 2`, hence is deficient.
-/

open scoped BigOperators

set_option maxRecDepth 40000

namespace Brockian.ZumkellerNumbers

/-- `n` is a *Zumkeller number* if it is positive and its set of divisors can be split into
two parts having the same sum. -/

theorem prod_lt_two_mul_prod_pred {n : ℕ} (hodd : Odd n) (hcard : n.primeFactors.card ≤ 2) :
    (∏ p ∈ n.primeFactors, p) < 2 * ∏ p ∈ n.primeFactors, (p - 1) := by
  have hp3 : ∀ p ∈ n.primeFactors, 3 ≤ p ∧ Odd p := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hpd
      obtain ⟨j, hj⟩ := hodd
      omega
    refine ⟨?_, hpp.odd_of_ne_two hp2⟩
    have := hpp.two_le
    omega
  interval_cases h : n.primeFactors.card
  · rw [Finset.card_eq_zero] at h
    simp [h]
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
    obtain ⟨h3, -⟩ := hp3 p (by rw [hp]; simp)
    rw [hp]
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp h
    obtain ⟨hp3', hpo⟩ := hp3 p (by rw [hs]; simp)
    obtain ⟨hq3', hqo⟩ := hp3 q (by rw [hs]; simp)
    rw [hs, Finset.prod_pair hpq, Finset.prod_pair hpq]
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    obtain ⟨ka, hka⟩ := hpo
    obtain ⟨kb, hkb⟩ := hqo
    have ha2 : 2 ≤ a := by omega
    have hb2 : 2 ≤ b := by omega
    have hne : a ≠ b := by omega
    have hor : 4 ≤ a ∨ 4 ≤ b := by omega
    rcases hor with h4 | h4 <;> nlinarith

/-- An odd number with at most two distinct prime factors is deficient: `σ(n) < 2n`. -/
