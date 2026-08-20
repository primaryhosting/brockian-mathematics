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

@[simp] theorem pdset_star (P : RegularExpression α) :
    pdset P.star = (pdset P).map (· * P.star) := rfl

section DecidableEq

variable [DecidableEq α]

/-- Antimirov's partial derivative: a list of regular expressions whose union describes the
left quotient by a single letter. -/
