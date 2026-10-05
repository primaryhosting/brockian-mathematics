/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

/-- The number of inputs on which `f` takes the value `true`. -/

lemma isConstant_iff {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsConstant f ↔ trueCount f = 0 ∨ trueCount f = 2 ^ n := by
  constructor
  · intro h
    by_cases hx : ∃ x, f x = true
    · obtain ⟨x, hxt⟩ := hx
      right
      have : ∀ y : Fin n → Bool, f y = true := fun y => (h y x).trans hxt
      simp [trueCount, this]
    · left
      push_neg at hx
      simp [trueCount, hx]
  · intro h
    rcases h with h | h
    · have : ∀ x : Fin n → Bool, f x ≠ true := by
        intro x hx
        have hmem : x ∈ (Finset.univ.filter fun x => f x = true) := by simp [hx]
        rw [Finset.card_eq_zero.mp h] at hmem
        simp at hmem
      intro x y
      simp [Bool.eq_false_iff.mpr (this x), Bool.eq_false_iff.mpr (this y)]
    · have hall : (Finset.univ.filter fun x : Fin n → Bool => f x = true) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [← card_domain n] at h
        exact h
      intro x y
      have hx : f x = true := by
        have : x ∈ (Finset.univ.filter fun x : Fin n → Bool => f x = true) := by
          rw [hall]; exact Finset.mem_univ x
        simpa using this
      have hy : f y = true := by
        have : y ∈ (Finset.univ.filter fun x : Fin n → Bool => f x = true) := by
          rw [hall]; exact Finset.mem_univ y
        simpa using this
      rw [hx, hy]

/-- **Deutsch–Jozsa.** A single query to the phase oracle for `f` suffices to decide
whether `f` is constant or balanced: the amplitude of the all-zeros outcome has
modulus `1` exactly when `f` is constant, and vanishes exactly when `f` is balanced.
Consequently, under the promise that `f` is constant or balanced, the outcome of the
single measurement determines which case holds. -/
