/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GaleStewart

universe u

variable {X : Type u}

/-- The list of the first `n` moves of the play `a`. -/

@[simp] lemma hist_length (a : ℕ → X) (n : ℕ) : (hist a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [hist, ih]

