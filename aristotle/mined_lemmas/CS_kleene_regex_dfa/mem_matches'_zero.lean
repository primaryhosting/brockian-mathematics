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


theorem mem_matches'_zero (x : List α) : x ∈ (0 : RegularExpression α).matches' ↔ False := Iff.rfl

