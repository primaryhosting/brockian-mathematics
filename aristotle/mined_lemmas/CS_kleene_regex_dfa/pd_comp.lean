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


@[simp] theorem PD_comp (P Q : RegularExpression α) :
    PD (P * Q) = (fun p => p * Q) '' PD P ∪ PD Q := rfl
omit [DecidableEq α] in
