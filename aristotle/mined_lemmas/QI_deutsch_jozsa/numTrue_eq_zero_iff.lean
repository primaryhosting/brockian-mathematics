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

lemma numTrue_eq_zero_iff {n : ℕ} (f : (Fin n → Bool) → Bool) :
    numTrue f = 0 ↔ ∀ x, f x = false := by
  rw [numTrue, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x; simpa using h (Finset.mem_univ x)
  · intro h x _; simp [h x]

