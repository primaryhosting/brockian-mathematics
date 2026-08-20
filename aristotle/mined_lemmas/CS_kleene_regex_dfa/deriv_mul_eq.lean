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

theorem deriv_mul_eq (P Q : RegularExpression α) (a : α) :
    (P * Q).deriv a =
      if P.matchEpsilon then P.deriv a * Q + Q.deriv a else P.deriv a * Q := rfl

/-- Antimirov's partial derivatives compute the same language as Brzozowski's derivative. -/
