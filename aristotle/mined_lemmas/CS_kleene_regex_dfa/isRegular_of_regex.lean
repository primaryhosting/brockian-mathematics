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

theorem isRegular_of_regex {r : RegularExpression α} {L : Language α} (h : r.matches' = L) :
    L.IsRegular := by
  classical
  exact Language.IsRegular.of_finite_range_leftQuotient
    (h ▸ finite_range_leftQuotient_matches' r)

end CS

import Mathlib

/-!
# Kleene's algorithm: from a DFA to a regular expression

Given a DFA over a finite alphabet, we construct (the language of) a regular expression
describing the accepted language, by the classical dynamic-programming argument over the
set of allowed intermediate states.
-/

namespace CS

open Language Computability

variable {α : Type} {σ : Type} {ι : Type}

/-- A language is *described by a regular expression*. -/
