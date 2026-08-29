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


theorem mem_matches'_char (b : α) (x : List α) : x ∈ (char b).matches' ↔ x = [b] := Iff.rfl

/-! ### Partial derivatives -/

variable [DecidableEq α]

/-- The Antimirov partial derivative of a regular expression with respect to a letter. -/
