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

theorem mem_leftQuotient_kstar (L : Language α) (x y : List α) :
    y ∈ (L∗).leftQuotient x ↔
      (x ∈ L∗ ∧ y ∈ L∗) ∨
        ∃ v, (∃ u, u ++ v = x ∧ v ≠ [] ∧ u ∈ L∗) ∧ y ∈ (L.leftQuotient v) * L∗ := by
  rw [mem_leftQuotient]
  constructor
  · rintro hxy
    obtain ⟨l, hl, hmem⟩ := Language.mem_kstar.1 hxy
    rcases kstar_split L l hmem x y hl.symm with h | ⟨u, v, r, s, huv, hv, hu, hvr, hs, hys⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, ⟨u, huv, hv, hu⟩, ⟨r, by rwa [mem_leftQuotient], s, hs, hys.symm⟩⟩
  · rintro (⟨hx, hy⟩ | ⟨v, ⟨u, huv, -, hu⟩, ⟨r, hr, s, hs, hrs⟩⟩)
    · exact mem_of_le (kstar_mul_kstar L).le (append_mem_mul hx hy)
    · rw [mem_leftQuotient] at hr
      have h2 : (v ++ r) ++ s ∈ L∗ := mem_of_le mul_kstar_le_kstar (append_mem_mul hr hs)
      have h3 : u ++ ((v ++ r) ++ s) ∈ L∗ := mem_of_le (kstar_mul_kstar L).le (append_mem_mul hu h2)
      have hxy : x ++ y = u ++ ((v ++ r) ++ s) := by
        rw [← huv, ← hrs]; simp [List.append_assoc]
      rwa [hxy]

