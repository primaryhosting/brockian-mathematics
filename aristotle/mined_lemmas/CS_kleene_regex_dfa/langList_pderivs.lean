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

theorem langList_pderivs (l : List (RegularExpression α)) (w : List α) :
    langList (pderivs l w) = (langList l).leftQuotient w := by
  induction w generalizing l with
  | nil => simp [pderivs]
  | cons a w ih =>
    rw [pderivs, ih, langList_pderivList, ← Language.leftQuotient_append]
    rfl

