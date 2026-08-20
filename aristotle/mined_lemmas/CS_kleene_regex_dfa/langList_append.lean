import Mathlib

/-!
# Antimirov partial derivatives and finiteness of left quotients

This file develops Antimirov's partial derivatives of a regular expression, and uses them to
show that a language described by a regular expression has only finitely many left quotients.
Combined with the Myhill–Nerode theorem this gives the "regular expression → DFA" direction of
Kleene's theorem.
-/

namespace CS

open RegularExpression

variable {α : Type*}

/-- The language of a set of regular expressions: the union of the languages they describe. -/

theorem langList_append (l₁ l₂ : List (RegularExpression α)) :
    langList (l₁ ++ l₂) = langList l₁ + langList l₂ := by
  ext w
  simp only [mem_langList, List.mem_append, Language.mem_add]
  constructor
  · rintro ⟨p, hp | hp, hw⟩
    · exact Or.inl ⟨p, hp, hw⟩
    · exact Or.inr ⟨p, hp, hw⟩
  · rintro (⟨p, hp, hw⟩ | ⟨p, hp, hw⟩)
    · exact ⟨p, Or.inl hp, hw⟩
    · exact ⟨p, Or.inr hp, hw⟩

