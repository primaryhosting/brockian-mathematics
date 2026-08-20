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

protected theorem mul {L₁ L₂ : Language α} (h₁ : IsRegexLang L₁) (h₂ : IsRegexLang L₂) :
    IsRegexLang (L₁ * L₂) := by
  obtain ⟨r₁, rfl⟩ := h₁
  obtain ⟨r₂, rfl⟩ := h₂
  exact ⟨r₁ * r₂, rfl⟩

