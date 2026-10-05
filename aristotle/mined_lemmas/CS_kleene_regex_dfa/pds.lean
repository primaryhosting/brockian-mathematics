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


def pds : RegularExpression α → List α → Set (RegularExpression α)
  | r, [] => {r}
  | r, a :: x => ⋃ p ∈ pd r a, pds p x

