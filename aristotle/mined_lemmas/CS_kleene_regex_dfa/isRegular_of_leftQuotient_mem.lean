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


theorem isRegular_of_leftQuotient_mem {L : Language α} {S : Set (Language α)}
    (hS : S.Finite) (h : ∀ x, L.leftQuotient x ∈ S) : L.IsRegular :=
  Language.IsRegular.of_finite_range_leftQuotient
    (hS.subset (by rintro _ ⟨x, rfl⟩; exact h x))

