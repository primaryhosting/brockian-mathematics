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

def pdset : RegularExpression α → List (RegularExpression α)
  | 0 => []
  | 1 => []
  | char _ => [1]
  | P + Q => pdset P ++ pdset Q
  | P * Q => (pdset P).map (· * Q) ++ pdset Q
  | RegularExpression.star P => (pdset P).map (· * RegularExpression.star P)

