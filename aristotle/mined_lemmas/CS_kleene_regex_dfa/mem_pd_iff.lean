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


theorem mem_pd_iff (P : RegularExpression α) (a : α) (y : List α) :
    (∃ p ∈ pd P a, y ∈ p.matches') ↔ a :: y ∈ P.matches' := by
  induction P generalizing y with
  | zero =>
      rw [RegularExpression.zero_def, pd_zero]
      simp
  | epsilon =>
      rw [RegularExpression.one_def, pd_one]
      simp
  | char b =>
      rw [pd_char, mem_matches'_char]
      by_cases h : a = b
      · subst h
        rw [if_pos rfl]
        constructor
        · rintro ⟨p, hp, hy⟩
          rw [Set.mem_singleton_iff] at hp
          subst hp
          rw [mem_matches'_one] at hy
          rw [hy]
        · intro hy
          rw [List.cons.injEq] at hy
          exact ⟨1, rfl, (mem_matches'_one y).2 hy.2⟩
      · rw [if_neg h]
        constructor
        · rintro ⟨p, hp, -⟩
          exact absurd hp (Set.notMem_empty p)
        · intro hy
          rw [List.cons.injEq] at hy
          exact absurd hy.1 h
  | plus P Q ihP ihQ =>
      rw [RegularExpression.plus_def, pd_plus]
      show (∃ p ∈ pd P a ∪ pd Q a, y ∈ p.matches') ↔ a :: y ∈ P.matches' + Q.matches'
      rw [show (a :: y ∈ P.matches' + Q.matches') ↔
          (a :: y ∈ P.matches' ∨ a :: y ∈ Q.matches') from Iff.rfl, ← ihP y, ← ihQ y]
      constructor
      · rintro ⟨p, hp | hp, hy⟩
        · exact Or.inl ⟨p, hp, hy⟩
        · exact Or.inr ⟨p, hp, hy⟩
      · rintro (⟨p, hp, hy⟩ | ⟨p, hp, hy⟩)
        · exact ⟨p, Or.inl hp, hy⟩
        · exact ⟨p, Or.inr hp, hy⟩
  | comp P Q ihP ihQ =>
      rw [RegularExpression.comp_def, pd_comp]
      show (∃ p ∈ (fun p => p * Q) '' pd P a ∪ (if P.matchEpsilon then pd Q a else ∅),
          y ∈ p.matches') ↔ a :: y ∈ P.matches' * Q.matches'
      rw [mem_mul_cons]
      constructor
      · rintro ⟨p, hp, hy⟩
        rcases hp with ⟨q, hq, rfl⟩ | hp
        · left
          obtain ⟨u, hu, v, hv, rfl⟩ := hy
          exact ⟨u, v, rfl, (ihP u).1 ⟨q, hq, hu⟩, hv⟩
        · right
          by_cases he : P.matchEpsilon = true
          · rw [if_pos he] at hp
            exact ⟨(nil_mem_matches'_iff P).2 he, (ihQ y).1 ⟨p, hp, hy⟩⟩
          · rw [if_neg he] at hp
            exact absurd hp (Set.notMem_empty p)
      · rintro (⟨u, v, rfl, hu, hv⟩ | ⟨h0, hy⟩)
        · obtain ⟨q, hq, hu⟩ := (ihP u).2 hu
          exact ⟨q * Q, Or.inl ⟨q, hq, rfl⟩, u, hu, v, hv, rfl⟩
        · obtain ⟨q, hq, hy⟩ := (ihQ y).2 hy
          have he : P.matchEpsilon = true := (nil_mem_matches'_iff P).1 h0
          exact ⟨q, Or.inr (by rw [if_pos he]; exact hq), hy⟩
  | star P ih =>
      rw [pd_star]
      show (∃ p ∈ (fun p => p * RegularExpression.star P) '' pd P a, y ∈ p.matches') ↔
        a :: y ∈ P.matches'∗
      rw [mem_kstar_cons]
      constructor
      · rintro ⟨p, ⟨q, hq, rfl⟩, hy⟩
        obtain ⟨u, hu, v, hv, rfl⟩ := hy
        exact ⟨u, v, rfl, (ih u).1 ⟨q, hq, hu⟩, hv⟩
      · rintro ⟨u, v, rfl, hu, hv⟩
        obtain ⟨q, hq, hu⟩ := (ih u).2 hu
        exact ⟨q * RegularExpression.star P, ⟨q, hq, rfl⟩, u, hu, v, hv, rfl⟩

/-- Partial derivatives with respect to a word. -/
