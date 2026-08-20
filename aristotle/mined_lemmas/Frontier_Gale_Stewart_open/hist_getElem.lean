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

lemma hist_getElem? (a : ℕ → X) : ∀ n i, i < n → (hist a n)[i]? = some (a i) := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
    · rw [hist_succ, List.getElem?_append_left (by simpa using h)]
      exact ih i h
    · subst h
      rw [hist_succ, List.getElem?_append_right (by simp)]
      simp

