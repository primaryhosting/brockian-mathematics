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

lemma hist_getD (a : ℕ → X) (d : X) {n i : ℕ} (hi : i < n) : (hist a n).getD i d = a i := by
  rw [List.getD_eq_getElem?_getD, hist_getElem? a n i hi]
  rfl

/-- Two plays with the same history of length `n` agree below `n`. -/
