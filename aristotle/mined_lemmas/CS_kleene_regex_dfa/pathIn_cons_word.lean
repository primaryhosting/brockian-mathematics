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


@[simp] theorem pathIn_cons_word (l : List σ) (s t : σ) (a : α) (x : List α) :
    PathIn M l s t (a :: x) ↔
      (M.step s a = t ∧ x = []) ∨ (M.step s a ∈ l ∧ PathIn M l (M.step s a) t x) := Iff.rfl

