/-
Antimirov partial derivatives: every language matched by a regular expression is regular
(i.e. accepted by a DFA with finitely many states).
-/
import Mathlib

namespace CS

open RegularExpression Language Computability

universe u
variable {α : Type u}

/-! ### Membership lemmas for languages -/


def unionLang (S : Set (RegularExpression α)) : Language α := {y | ∃ p ∈ S, y ∈ p.matches'}

omit [DecidableEq α] in
