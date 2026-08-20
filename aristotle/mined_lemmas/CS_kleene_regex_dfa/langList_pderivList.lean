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

theorem langList_pderivList (l : List (RegularExpression α)) (a : α) :
    langList (pderivList l a) = (langList l).leftQuotient [a] := by
  ext w
  simp only [pderivList, mem_langList, List.mem_flatMap, Language.mem_leftQuotient,
    List.singleton_append]
  constructor
  · rintro ⟨q, ⟨p, hp, hq⟩, hw⟩
    refine ⟨p, hp, (mem_matches'_deriv p a w).1 ?_⟩
    rw [← langList_pderiv]
    exact ⟨q, hq, hw⟩
  · rintro ⟨p, hp, hw⟩
    have : w ∈ langList (pderiv p a) := by
      rw [langList_pderiv]; exact (mem_matches'_deriv p a w).2 hw
    obtain ⟨q, hq, hw'⟩ := this
    exact ⟨q, ⟨p, hp, hq⟩, hw'⟩

