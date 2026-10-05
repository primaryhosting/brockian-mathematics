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


theorem matches'_pathRegex : ∀ (l : List σ) (s t : σ),
    (pathRegex M l s t).matches' = pathLang M l s t := by
  intro l
  induction l with
  | nil =>
    intro s t
    rw [pathRegex, matches'_baseRegex]
  | cons q qs ih =>
    intro s t
    rw [pathRegex, RegularExpression.matches'_add, RegularExpression.matches'_mul,
      RegularExpression.matches'_mul, RegularExpression.matches'_star, ih, ih, ih, ih,
      pathLang_cons]

/-- Every DFA over a finite alphabet with finitely many states has its language described by a
regular expression. -/
