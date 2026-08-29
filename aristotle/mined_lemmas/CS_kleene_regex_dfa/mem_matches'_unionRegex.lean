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


theorem mem_matches'_unionRegex (f : σ → RegularExpression α) (l : List σ) (x : List α) :
    x ∈ (unionRegex f l).matches' ↔ ∃ q ∈ l, x ∈ (f q).matches' := by
  induction l with
  | nil =>
    rw [unionRegex, List.foldr_nil, RegularExpression.matches'_zero]
    simp
  | cons q l ih =>
    have hcons : unionRegex f (q :: l) = f q + unionRegex f l := rfl
    rw [hcons, RegularExpression.matches'_add, mem_add_language, ih]
    simp

variable [Fintype α] [DecidableEq σ]

/-- The regular expression for paths with no intermediate states. -/
