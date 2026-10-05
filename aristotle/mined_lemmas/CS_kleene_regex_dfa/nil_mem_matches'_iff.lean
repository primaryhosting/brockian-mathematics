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


theorem nil_mem_matches'_iff (P : RegularExpression α) :
    [] ∈ P.matches' ↔ P.matchEpsilon = true := by
  rw [← P.rmatch_iff_matches' []]
  rfl

/-- Correctness of the partial derivative: the languages of the partial derivatives of `P`
with respect to `a` cover exactly the words `y` with `a :: y` matched by `P`. -/
