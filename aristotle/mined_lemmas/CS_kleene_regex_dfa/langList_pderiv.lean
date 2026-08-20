import Mathlib

/-!
# Antimirov partial derivatives and finiteness of left quotients

This file develops Antimirov's partial derivatives of a regular expression, and uses them to
show that a language described by a regular expression has only finitely many left quotients.
Combined with the Myhill–Nerode theorem this gives the "regular expression → DFA" direction of
Kleene's theorem.
-/

namespace CS

open RegularExpression

variable {α : Type*}

/-- The language of a set of regular expressions: the union of the languages they describe. -/

theorem langList_pderiv (P : RegularExpression α) (a : α) :
    langList (pderiv P a) = (P.deriv a).matches' := by
  induction P with
  | zero => rw [zero_def]; simp
  | epsilon => rw [one_def]; simp
  | char b =>
    rw [pderiv_char]
    by_cases h : b = a
    · subst h
      rw [if_pos rfl, RegularExpression.deriv_char_self, langList_singleton]
    · rw [if_neg h, RegularExpression.deriv_char_of_ne h, langList_nil]
      rfl
  | plus P Q ihP ihQ =>
    rw [plus_def, pderiv_add, langList_append, ihP, ihQ, RegularExpression.deriv_add]
    simp
  | comp P Q ihP ihQ =>
    rw [comp_def, pderiv_mul, langList_append, langList_map_mul, ihP]
    by_cases h : P.matchEpsilon
    · rw [if_pos h, ihQ, deriv_mul_eq, if_pos h]
      simp
    · rw [if_neg h, deriv_mul_eq, if_neg h]
      simp
  | star P ihP =>
    rw [pderiv_star, langList_map_mul, ihP, RegularExpression.deriv_star]
    simp

