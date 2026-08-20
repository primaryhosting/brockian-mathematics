import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-- The sign `(-1)^b` attached to a boolean. -/

theorem amp_eq_zero_of_balanced {n : ℕ} (f : (Fin n → Bool) → Bool) (h : IsBalanced f) :
    amp f (zeroStr n) = 0 := by
  have hc := card_true_add_card_false f
  unfold IsBalanced at h
  have : (univ.filter fun x : Fin n → Bool => f x = false).card
      = (univ.filter fun x => f x = true).card := by omega
  rw [amp_zeroStr, this]
  simp

/-- Conversely, a vanishing amplitude forces the function to be balanced. -/
