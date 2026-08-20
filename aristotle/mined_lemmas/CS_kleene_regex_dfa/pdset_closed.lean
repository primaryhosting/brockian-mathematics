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

theorem pdset_closed {P : RegularExpression α} :
    ∀ {p : RegularExpression α}, p ∈ pdset P → ∀ {a : α} {q : RegularExpression α},
      q ∈ pderiv p a → q ∈ pdset P := by
  induction P with
  | zero => intro p hp; rw [zero_def, pdset_zero] at hp; simp at hp
  | epsilon => intro p hp; rw [one_def, pdset_one] at hp; simp at hp
  | char b =>
    intro p hp a q hq
    rw [pdset_char, List.mem_singleton] at hp
    subst hp
    rw [pderiv_one] at hq
    simp at hq
  | plus P Q ihP ihQ =>
    intro p hp a q hq
    rw [plus_def, pdset_add, List.mem_append] at hp
    rw [plus_def, pdset_add, List.mem_append]
    rcases hp with hp | hp
    · exact Or.inl (ihP hp hq)
    · exact Or.inr (ihQ hp hq)
  | comp P Q ihP ihQ =>
    intro p hp a q hq
    rw [comp_def, pdset_mul, List.mem_append] at hp
    rw [comp_def, pdset_mul, List.mem_append]
    rcases hp with hp | hp
    · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
      rw [pderiv_mul, List.mem_append] at hq
      rcases hq with hq | hq
      · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        exact Or.inl (List.mem_map.2 ⟨q', ihP hp' hq', rfl⟩)
      · split_ifs at hq with hc
        · exact Or.inr (pderiv_mem_pdset hq)
        · simp at hq
    · exact Or.inr (ihQ hp hq)
  | star P ihP =>
    intro p hp a q hq
    rw [pdset_star] at hp
    rw [pdset_star]
    obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
    rw [pderiv_mul, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      exact List.mem_map.2 ⟨q', ihP hp' hq', rfl⟩
    · split_ifs at hq with hc
      · rw [pderiv_star] at hq
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        exact List.mem_map.2 ⟨q', pderiv_mem_pdset hq', rfl⟩
      · simp at hq

