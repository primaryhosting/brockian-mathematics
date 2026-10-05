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


theorem mem_kstar_cons (L : Language α) (a : α) (y : List α) :
    a :: y ∈ L∗ ↔ ∃ u v, u ++ v = y ∧ a :: u ∈ L ∧ v ∈ L∗ := by
  constructor
  · intro h
    rw [Language.mem_kstar_iff_exists_nonempty] at h
    obtain ⟨S, hS, hmem⟩ := h
    cases S with
    | nil => simp at hS
    | cons u S =>
      obtain ⟨hu, hune⟩ := hmem u (by simp)
      cases u with
      | nil => exact absurd rfl hune
      | cons b u =>
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hS
        obtain ⟨rfl, rfl⟩ := hS
        refine ⟨u, S.flatten, rfl, hu, ?_⟩
        exact Language.mem_kstar_iff_exists_nonempty.2 ⟨S, rfl, fun z hz => hmem z (by simp [hz])⟩
  · rintro ⟨u, v, rfl, hu, hv⟩
    have hmem : (a :: u) ++ v ∈ L * L∗ := ⟨a :: u, hu, v, hv, rfl⟩
    exact KleeneAlgebra.mul_kstar_le_kstar L hmem

