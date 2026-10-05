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


def PathIn (M : DFA α σ) (l : List σ) : σ → σ → List α → Prop
  | s, t, [] => s = t
  | s, t, (a :: x) => (M.step s a = t ∧ x = []) ∨ (M.step s a ∈ l ∧ PathIn M l (M.step s a) t x)

/-- The language of words labelling a path from `s` to `t` with intermediate states in `l`. -/
