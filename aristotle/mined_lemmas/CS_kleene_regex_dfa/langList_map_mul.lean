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

theorem langList_map_mul (l : List (RegularExpression α)) (Q : RegularExpression α) :
    langList (l.map (· * Q)) = langList l * Q.matches' := by
  ext w
  simp only [mem_langList, List.mem_map, Language.mem_mul]
  constructor
  · rintro ⟨p, ⟨p', hp', rfl⟩, u, hu, v, hv, rfl⟩
    exact ⟨u, ⟨p', hp', hu⟩, v, hv, rfl⟩
  · rintro ⟨u, ⟨p', hp', hu⟩, v, hv, rfl⟩
    exact ⟨p' * Q, ⟨p', hp', rfl⟩, u, hu, v, hv, rfl⟩

/-- The (finite) Antimirov set of a regular expression: a list containing every regular
expression reachable by iterated partial derivatives. -/
