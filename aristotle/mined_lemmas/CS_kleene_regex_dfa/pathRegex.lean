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


noncomputable def pathRegex : List σ → σ → σ → RegularExpression α
  | [], s, t => baseRegex M s t
  | q :: qs, s, t =>
      pathRegex qs s t + pathRegex qs s q * (pathRegex qs q q).star * pathRegex qs q t

