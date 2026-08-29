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


def PD : RegularExpression α → Set (RegularExpression α)
  | 0 => ∅
  | 1 => ∅
  | char _ => {1}
  | P + Q => PD P ∪ PD Q
  | P * Q => (fun p => p * Q) '' PD P ∪ PD Q
  | RegularExpression.star P => (fun p => p * RegularExpression.star P) '' PD P

omit [DecidableEq α] in
