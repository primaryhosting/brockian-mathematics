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


theorem PD_finite (P : RegularExpression α) : (PD P).Finite := by
  induction P with
  | zero => rw [RegularExpression.zero_def, PD_zero]; exact Set.finite_empty
  | epsilon => rw [RegularExpression.one_def, PD_one]; exact Set.finite_empty
  | char b => rw [PD_char]; exact Set.finite_singleton _
  | plus P Q ihP ihQ => rw [RegularExpression.plus_def, PD_plus]; exact ihP.union ihQ
  | comp P Q ihP ihQ => rw [RegularExpression.comp_def, PD_comp]; exact (ihP.image _).union ihQ
  | star P ih => rw [PD_star]; exact ih.image _

