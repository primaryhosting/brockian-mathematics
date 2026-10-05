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


noncomputable def baseRegex (s t : σ) : RegularExpression α :=
  (if s = t then 1 else 0) +
    letterRegex ((Finset.univ.filter (fun a : α => M.step s a = t)).toList)

