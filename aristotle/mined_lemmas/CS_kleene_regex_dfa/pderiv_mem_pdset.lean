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

theorem pderiv_mem_pdset {P : RegularExpression α} {a : α} {q : RegularExpression α}
    (h : q ∈ pderiv P a) : q ∈ pdset P := by
  induction P generalizing q with
  | zero => rw [zero_def, pderiv_zero] at h; simp at h
  | epsilon => rw [one_def, pderiv_one] at h; simp at h
  | char b =>
    rw [pderiv_char] at h
    by_cases hb : b = a
    · rw [if_pos hb] at h
      simpa [pdset_char] using h
    · rw [if_neg hb] at h; simp at h
  | plus P Q ihP ihQ =>
    rw [plus_def, pderiv_add, List.mem_append] at h
    rw [plus_def, pdset_add, List.mem_append]
    rcases h with h | h
    · exact Or.inl (ihP h)
    · exact Or.inr (ihQ h)
  | comp P Q ihP ihQ =>
    rw [comp_def, pderiv_mul, List.mem_append] at h
    rw [comp_def, pdset_mul, List.mem_append]
    rcases h with h | h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact Or.inl (List.mem_map.2 ⟨p, ihP hp, rfl⟩)
    · split_ifs at h with hc
      · exact Or.inr (ihQ h)
      · simp at h
  | star P ihP =>
    rw [pderiv_star] at h
    rw [pdset_star]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact List.mem_map.2 ⟨p, ihP hp, rfl⟩

/-- The Antimirov set is closed under partial derivatives. -/
