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


@[simp] theorem PD_star (P : RegularExpression α) :
    PD (RegularExpression.star P) = (fun p => p * RegularExpression.star P) '' PD P := rfl

omit [DecidableEq α] in
