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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* when its set of divisors can be split into
two parts with equal sums, i.e. there is `S ⊆ n.divisors` whose sum is half of `σ₁ n`. -/

theorem prod_lt_two_mul_prod_sub_one {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ Odd p)
    (hcard : s.card ≤ 2) : ∏ p ∈ s, p < 2 * ∏ p ∈ s, (p - 1) := by
  interval_cases h : s.card
  · rw [Finset.card_eq_zero] at h
    subst h
    simp
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.1 h
    obtain ⟨hp, hodd⟩ := hs p (by simp)
    have h3 : 3 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge p 3 with h' | h'
      · interval_cases p
        simp_all [Nat.odd_iff]
      · exact h'
    simp only [Finset.prod_singleton]
    omega
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 h
    obtain ⟨hp, hop⟩ := hs p (by simp)
    obtain ⟨hq, hoq⟩ := hs q (by simp)
    have h3p : 3 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge p 3 with h' | h'
      · interval_cases p
        simp_all [Nat.odd_iff]
      · exact h'
    have h3q : 3 ≤ q := by
      have := hq.two_le
      rcases Nat.lt_or_ge q 3 with h' | h'
      · interval_cases q
        simp_all [Nat.odd_iff]
      · exact h'
    have h5 : 5 ≤ p ∨ 5 ≤ q := by
      rcases Nat.lt_or_ge p 5 with h' | h'
      · rcases Nat.lt_or_ge q 5 with h'' | h''
        · interval_cases p <;> interval_cases q <;> simp_all [Nat.odd_iff]
        · exact Or.inr h''
      · exact Or.inl h'
    rw [Finset.prod_pair hpq, Finset.prod_pair hpq]
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rcases h5 with h5 | h5
    · nlinarith
    · nlinarith

/-- An odd Zumkeller number has at least three distinct prime factors. -/
