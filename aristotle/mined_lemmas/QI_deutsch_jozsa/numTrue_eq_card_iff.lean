/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QI

open Finset

/-- The sign `(-1)^(f x)` attached to a Boolean value. -/

lemma numTrue_eq_card_iff {n : ℕ} (f : (Fin n → Bool) → Bool) :
    numTrue f = 2 ^ n ↔ ∀ x, f x = true := by
  constructor
  · intro h
    have hsub : (univ.filter fun x => f x = true) = (univ : Finset (Fin n → Bool)) := by
      apply Finset.eq_univ_of_card
      simpa [numTrue] using h
    intro x
    have : x ∈ (univ.filter fun x => f x = true) := by rw [hsub]; exact Finset.mem_univ x
    simpa using this
  · intro h
    have : (univ.filter fun x => f x = true) = (univ : Finset (Fin n → Bool)) := by
      apply Finset.filter_true_of_mem
      intro x _; exact h x
    rw [numTrue, this, card_domain]

