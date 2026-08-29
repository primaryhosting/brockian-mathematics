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


@[simp] theorem PD_one : PD (1 : RegularExpression α) = ∅ := rfl
omit [DecidableEq α] in
