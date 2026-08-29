import Mathlib

/-!
# Kleene Regex Dfa
Category: Computer Science
Target: CS.kleene_regex_dfa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Kleene's theorem: over a finite alphabet, a language is denoted by a regular expression
if and only if it is accepted by a deterministic finite automaton with finitely many states.
-/

open Language Computability

namespace CS

variable {α : Type*}


theorem mem_matches'_letterRegex (l : List α) (x : List α) :
    x ∈ (letterRegex l).matches' ↔ ∃ a ∈ l, x = [a] := by
  induction l with
  | nil =>
    rw [letterRegex, List.foldr_nil, RegularExpression.matches'_zero]
    simp
  | cons a l ih =>
    have hcons : letterRegex (a :: l) = RegularExpression.char a + letterRegex l := rfl
    rw [hcons, RegularExpression.matches'_add, RegularExpression.matches'_char,
      mem_add_language, ih]
    simp

/-- A finite union of regular expressions indexed by a list. -/
