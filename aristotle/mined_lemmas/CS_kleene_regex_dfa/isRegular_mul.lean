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

theorem isRegular_mul {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ * L₂).IsRegular := by
  rw [isRegular_iff_finite_range_leftQuotient] at h₁ h₂ ⊢
  refine Set.Finite.subset (s := (fun p : Language α × Set (Language α) => p.1 * L₂ + unionOf p.2)
    '' (Set.range L₁.leftQuotient ×ˢ {T | T ⊆ Set.range L₂.leftQuotient}))
    ((h₁.prod h₂.finite_subsets).image _) ?_
  rw [Set.range_subset_iff]
  intro x
  refine ⟨(L₁.leftQuotient x,
    {N | ∃ v, (∃ u, u ++ v = x ∧ u ∈ L₁) ∧ N = L₂.leftQuotient v}), ⟨⟨x, rfl⟩, ?_⟩, ?_⟩
  · rintro N ⟨v, -, rfl⟩
    exact ⟨v, rfl⟩
  · ext y
    rw [mem_leftQuotient_mul, Language.mem_add]
    simp only [mem_unionOf, Set.mem_setOf_eq]
    constructor
    · rintro (h | ⟨N, ⟨v, hv, rfl⟩, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, hy⟩
    · rintro (h | ⟨v, hv, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_, ⟨v, hv, rfl⟩, hy⟩

/-! ### Kleene star -/

/-- Splitting a word of `L∗` along a prefix: either the prefix is itself in `L∗`, or the prefix
ends strictly inside one of the factors. -/
