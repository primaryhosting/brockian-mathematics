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


theorem mem_mul_cons (L M : Language α) (a : α) (y : List α) :
    a :: y ∈ L * M ↔
      (∃ u v, u ++ v = y ∧ a :: u ∈ L ∧ v ∈ M) ∨ ([] ∈ L ∧ a :: y ∈ M) := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    cases u with
    | nil =>
      right
      simp only [List.nil_append] at huv
      exact ⟨hu, huv ▸ hv⟩
    | cons b u =>
      left
      simp only [List.cons_append, List.cons.injEq] at huv
      obtain ⟨rfl, rfl⟩ := huv
      exact ⟨u, v, rfl, hu, hv⟩
  · rintro (⟨u, v, rfl, hu, hv⟩ | ⟨h0, h⟩)
    · exact ⟨a :: u, hu, v, hv, rfl⟩
    · exact ⟨[], h0, a :: y, h, rfl⟩

