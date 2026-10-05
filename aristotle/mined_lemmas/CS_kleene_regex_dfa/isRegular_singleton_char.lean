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


theorem isRegular_singleton_char (a : α) : ({[a]} : Language α).IsRegular := by
  refine isRegular_of_leftQuotient_mem (S := {0, 1, {[a]}}) (Set.toFinite _) fun x => ?_
  match x with
  | [] =>
    right; right
    ext y
    simp
  | b :: x =>
    by_cases hb : b = a
    · subst hb
      match x with
      | [] =>
        right; left
        ext y
        simp
      | c :: x =>
        left
        ext y
        simp
    · left
      ext y
      simp [hb]

/-- Left quotients of a concatenation. -/
