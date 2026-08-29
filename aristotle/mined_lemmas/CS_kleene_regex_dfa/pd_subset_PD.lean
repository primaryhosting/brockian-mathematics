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


theorem pd_subset_PD (P : RegularExpression α) (a : α) : pd P a ⊆ PD P := by
  induction P with
  | zero => rw [RegularExpression.zero_def, PD_zero, pd_zero]
  | epsilon => rw [RegularExpression.one_def, PD_one, pd_one]
  | char b =>
      rw [pd_char, PD_char]
      by_cases h : a = b
      · rw [if_pos h]
      · rw [if_neg h]; exact Set.empty_subset _
  | plus P Q ihP ihQ =>
      rw [RegularExpression.plus_def, PD_plus, pd_plus]
      exact Set.union_subset_union ihP ihQ
  | comp P Q ihP ihQ =>
      rw [RegularExpression.comp_def, PD_comp, pd_comp]
      refine Set.union_subset_union (Set.image_mono ihP) ?_
      by_cases he : P.matchEpsilon = true
      · rw [if_pos he]; exact ihQ
      · rw [if_neg he]; exact Set.empty_subset _
  | star P ih =>
      rw [PD_star, pd_star]
      exact Set.image_mono ih

