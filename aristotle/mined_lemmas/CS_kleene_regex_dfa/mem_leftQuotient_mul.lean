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

theorem mem_leftQuotient_mul (L₁ L₂ : Language α) (x y : List α) :
    y ∈ (L₁ * L₂).leftQuotient x ↔
      y ∈ (L₁.leftQuotient x) * L₂ ∨
        ∃ v, (∃ u, u ++ v = x ∧ u ∈ L₁) ∧ y ∈ L₂.leftQuotient v := by
  simp only [mem_leftQuotient, Language.mem_mul]
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    rcases List.append_eq_append_iff.1 hpq with ⟨as, hx, hq'⟩ | ⟨bs, hp', hy⟩
    · exact Or.inr ⟨as, ⟨p, hx.symm, hp⟩, by rw [← hq']; exact hq⟩
    · exact Or.inl ⟨bs, by rw [← hp']; exact hp, q, hq, hy.symm⟩
  · rintro (⟨b, hb, c, hc, hbc⟩ | ⟨v, ⟨u, huv, hu⟩, hy⟩)
    · exact ⟨x ++ b, hb, c, hc, by rw [List.append_assoc, hbc]⟩
    · exact ⟨u, hu, v ++ y, hy, by rw [← List.append_assoc, huv]⟩

