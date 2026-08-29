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

theorem isRegular_kstar {L : Language α} (h : L.IsRegular) : (L∗).IsRegular := by
  rw [isRegular_iff_finite_range_leftQuotient] at h ⊢
  refine Set.Finite.subset (s := (fun p : Bool × Set (Language α) =>
      condLang p.1 (L∗) + unionOf ((fun N => N * L∗) '' p.2))
    '' (Set.univ ×ˢ {T | T ⊆ Set.range L.leftQuotient}))
    ((Set.finite_univ.prod h.finite_subsets).image _) ?_
  rw [Set.range_subset_iff]
  intro x
  classical
  refine ⟨(decide (x ∈ L∗),
    {N | ∃ v, (∃ u, u ++ v = x ∧ v ≠ [] ∧ u ∈ L∗) ∧ N = L.leftQuotient v}),
    ⟨Set.mem_univ _, ?_⟩, ?_⟩
  · rintro N ⟨v, -, rfl⟩
    exact ⟨v, rfl⟩
  · ext y
    rw [mem_leftQuotient_kstar, Language.mem_add]
    simp only [mem_unionOf, mem_condLang, Set.mem_image, Set.mem_setOf_eq, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨N, ⟨M, ⟨v, hv, rfl⟩, rfl⟩, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, hy⟩
    · rintro (h | ⟨v, hv, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, hy⟩

/-! ### Main result -/

/-- **Kleene's theorem, easy direction**: the language of a regular expression is regular,
i.e. accepted by a finite DFA. -/
