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

def pderiv : RegularExpression α → α → List (RegularExpression α)
  | 0, _ => []
  | 1, _ => []
  | char b, a => if b = a then [1] else []
  | P + Q, a => pderiv P a ++ pderiv Q a
  | P * Q, a => (pderiv P a).map (· * Q) ++ (if P.matchEpsilon then pderiv Q a else [])
  | RegularExpression.star P, a => (pderiv P a).map (· * RegularExpression.star P)

