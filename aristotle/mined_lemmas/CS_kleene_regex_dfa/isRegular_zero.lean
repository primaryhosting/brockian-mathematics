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

theorem isRegular_zero : (0 : Language α).IsRegular := by
  rw [isRegular_iff_finite_range_leftQuotient]
  refine Set.Finite.subset (Set.finite_singleton (0 : Language α)) ?_
  rw [Set.range_subset_iff]
  intro x
  simp only [Set.mem_singleton_iff]
  ext y
  simp [leftQuotient, Language, Language.zero_def]

