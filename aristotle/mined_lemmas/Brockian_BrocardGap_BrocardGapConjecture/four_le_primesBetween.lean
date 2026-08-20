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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

open Finset

/-- **Oppermann's conjecture**: for every `m > 1` there is a prime strictly between
`m² - m` and `m²`, and a prime strictly between `m²` and `m² + m`. -/

lemma four_le_primesBetween {a b p₁ p₂ p₃ p₄ : ℕ}
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime) (h₄ : p₄.Prime)
    (ha : a < p₁) (o₁ : p₁ < p₂) (o₂ : p₂ < p₃) (o₃ : p₃ < p₄) (hb : p₄ < b) :
    4 ≤ primesBetween a b := by
  have hsub : ({p₁, p₂, p₃, p₄} : Finset ℕ) ⊆ (Finset.Ioo a b).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨⟨ha, by omega⟩, h₁⟩
    · exact ⟨⟨by omega, by omega⟩, h₂⟩
    · exact ⟨⟨by omega, by omega⟩, h₃⟩
    · exact ⟨⟨by omega, hb⟩, h₄⟩
  have hcard : ({p₁, p₂, p₃, p₄} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  calc (4 : ℕ) = ({p₁, p₂, p₃, p₄} : Finset ℕ).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Consecutive odd primes differ by at least `2`. -/
