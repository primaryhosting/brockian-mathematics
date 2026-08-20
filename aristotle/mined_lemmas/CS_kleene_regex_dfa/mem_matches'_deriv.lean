import Mathlib

/-!
# Antimirov partial derivatives and finiteness of left quotients

This file develops Antimirov's partial derivatives of a regular expression, and uses them to
show that a language described by a regular expression has only finitely many left quotients.
Combined with the Myhill–Nerode theorem this gives the "regular expression → DFA" direction of
Kleene's theorem.
-/

namespace CS

open RegularExpression

variable {α : Type*}

/-- The language of a set of regular expressions: the union of the languages they describe. -/

theorem mem_matches'_deriv (P : RegularExpression α) (a : α) (w : List α) :
    w ∈ (P.deriv a).matches' ↔ a :: w ∈ P.matches' := by
  rw [← rmatch_iff_matches', ← rmatch_iff_matches']
  rfl

