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

lemma amp_zeroStr {n : ℕ} (f : (Fin n → Bool) → Bool) :
    amp f (zeroStr n) = (1 / 2 ^ n) *
      (((univ.filter fun x => f x = false).card : ℝ)
        - ((univ.filter fun x => f x = true).card : ℝ)) := by
  unfold amp
  rw [← sum_sign]
  simp [phase_zero]

/-- **Balanced case**: the amplitude of the all-zeros outcome vanishes. -/
