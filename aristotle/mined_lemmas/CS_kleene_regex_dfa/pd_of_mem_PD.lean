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


theorem pd_of_mem_PD (P : RegularExpression α) (a : α) :
    ∀ p ∈ PD P, pd p a ⊆ PD P := by
  induction P with
  | zero =>
      intro p hp
      rw [RegularExpression.zero_def, PD_zero] at hp
      exact absurd hp (Set.notMem_empty p)
  | epsilon =>
      intro p hp
      rw [RegularExpression.one_def, PD_one] at hp
      exact absurd hp (Set.notMem_empty p)
  | char b =>
      intro p hp
      rw [PD_char, Set.mem_singleton_iff] at hp
      subst hp
      rw [pd_one]
      exact Set.empty_subset _
  | plus P Q ihP ihQ =>
      intro p hp
      rw [RegularExpression.plus_def, PD_plus] at hp ⊢
      rcases hp with hp | hp
      · exact (ihP p hp).trans Set.subset_union_left
      · exact (ihQ p hp).trans Set.subset_union_right
  | comp P Q ihP ihQ =>
      intro p hp
      rw [RegularExpression.comp_def, PD_comp] at hp ⊢
      rcases hp with ⟨q, hq, rfl⟩ | hp
      · intro s hs
        rw [pd_comp] at hs
        rcases hs with ⟨t, ht, rfl⟩ | hs
        · exact Or.inl ⟨t, ihP q hq ht, rfl⟩
        · by_cases he : q.matchEpsilon = true
          · rw [if_pos he] at hs
            exact Or.inr (pd_subset_PD Q a hs)
          · rw [if_neg he] at hs
            exact absurd hs (Set.notMem_empty s)
      · exact (ihQ p hp).trans Set.subset_union_right
  | star P ih =>
      intro p hp
      rw [PD_star] at hp ⊢
      obtain ⟨q, hq, rfl⟩ := hp
      intro s hs
      rw [pd_comp] at hs
      rcases hs with ⟨t, ht, rfl⟩ | hs
      · exact ⟨t, ih q hq ht, rfl⟩
      · by_cases he : q.matchEpsilon = true
        · rw [if_pos he] at hs
          rw [pd_star] at hs
          exact Set.image_mono (pd_subset_PD P a) hs
        · rw [if_neg he] at hs
          exact absurd hs (Set.notMem_empty s)

