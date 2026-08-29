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

open Finset

namespace Brockian.UnitaryPerfect

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/

theorem two_le_card_primeFactors {n : ℕ} (hn : IsUnitaryPerfect n) :
    2 ≤ n.primeFactors.card := by
  obtain ⟨hpos, hper⟩ := hn
  have hn0 : n ≠ 0 := hpos.ne'
  by_contra hcard
  push_neg at hcard
  interval_cases hc : n.primeFactors.card
  · have : n.primeFactors = ∅ := Finset.card_eq_zero.1 hc
    have hn1 : n = 1 := by
      rcases Nat.primeFactors_eq_empty.1 this with h | h
      · exact absurd h hn0
      · exact h
    rw [hn1] at hper
    simp at hper
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hc
    have hval : n = p ^ n.factorization p := by
      have := prod_primeFactors_pow_factorization hn0
      rw [hp, Finset.prod_singleton] at this
      exact this.symm
    have hsig : sigmaStar n = 1 + p ^ n.factorization p := by
      rw [sigmaStar_eq_prod hn0, hp, Finset.prod_singleton]
    have hkey : 1 + p ^ n.factorization p = 2 * n := by rw [← hsig, hper]
    have hn1 : n = 1 := by omega
    rw [hn1] at hc
    simp at hc

/-- Subbarao's observation: every unitary perfect number is even. -/
