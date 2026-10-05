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

theorem isRegular_singleton (a : α) : ({[a]} : Language α).IsRegular := by
  rw [isRegular_iff_finite_range_leftQuotient]
  refine Set.Finite.subset (Set.toFinite {({[a]} : Language α), 1, 0}) ?_
  rw [Set.range_subset_iff]
  intro x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  match x with
  | [] => left; ext y; simp [leftQuotient, Language]
  | [b] =>
      by_cases hb : b = a
      · subst hb
        right; left
        ext y
        simp [leftQuotient, Language, Language.one_def]
      · right; right
        ext y
        simp [leftQuotient, Language, Language.zero_def, hb]
  | b :: c :: t =>
      right; right
      ext y
      simp [leftQuotient, Language, Language.zero_def]

/-! ### Concatenation -/

/-- Membership in the left quotient of a product: either `x` consumes a prefix of the first
factor, or the whole first factor lies inside `x`. -/
