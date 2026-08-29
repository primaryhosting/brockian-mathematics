import Mathlib

/-!
# Regular expressions define regular languages

This file proves the "easy" direction of Kleene's theorem: the language matched by a regular
expression is accepted by some DFA with finitely many states (`Language.IsRegular`).

The proof goes through the Myhill–Nerode characterisation
`Language.isRegular_iff_finite_range_leftQuotient`: a language is regular iff it has finitely
many left quotients.
-/

open Language Computability

namespace Kleene

variable {α : Type*}

/-- The union of a family of languages, as a language. -/

theorem mem_unionOf {T : Set (Language α)} {y : List α} :
    y ∈ unionOf T ↔ ∃ N ∈ T, y ∈ N := Iff.rfl

/-- `L` if `b` is true, the empty language otherwise. -/
