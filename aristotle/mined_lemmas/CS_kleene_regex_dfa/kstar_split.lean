import Mathlib

/-!
# Regular expressions define regular languages

This file proves the "easy" direction of Kleene's theorem: the language matched by a regular
expression is accepted by some DFA with finitely many states (`Language.IsRegular`).

The proof goes through the Myhill–Nerode characterisation
`Language.isRegular_iff_finite_range_leftQuotient`: a language is regular iff it has finitely
many left quotients.
-/

open Language Computability

namespace Kleene

variable {α : Type*}

/-- The union of a family of languages, as a language. -/

theorem kstar_split (L : Language α) :
    ∀ (l : List (List α)), (∀ y ∈ l, y ∈ L) → ∀ (x w : List α), l.flatten = x ++ w →
      (x ∈ L∗ ∧ w ∈ L∗) ∨
        ∃ u v r s, u ++ v = x ∧ v ≠ [] ∧ u ∈ L∗ ∧ v ++ r ∈ L ∧ s ∈ L∗ ∧ w = r ++ s := by
  intro l
  induction l with
  | nil =>
      intro _ x w h
      rw [List.flatten_nil] at h
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
      exact Or.inl ⟨nil_mem_kstar L, nil_mem_kstar L⟩
  | cons z l ih =>
      intro hl x w h
      have hz : z ∈ L := hl z (by simp)
      have hl' : ∀ y ∈ l, y ∈ L := fun y hy => hl y (by simp [hy])
      rw [List.flatten_cons] at h
      rcases List.append_eq_append_iff.1 h with ⟨as, hx, hfl⟩ | ⟨bs, hz', hw⟩
      · rcases ih hl' as w hfl with ⟨h1, h2⟩ | ⟨u, v, r, s, huv, hv, hu, hvr, hs, hws⟩
        · refine Or.inl ⟨?_, h2⟩
          rw [hx]
          exact mem_of_le mul_kstar_le_kstar (append_mem_mul hz h1)
        · refine Or.inr ⟨z ++ u, v, r, s, ?_, hv, ?_, hvr, hs, hws⟩
          · rw [List.append_assoc, huv, ← hx]
          · exact mem_of_le mul_kstar_le_kstar (append_mem_mul hz hu)
      · rcases eq_or_ne x [] with rfl | hx
        · refine Or.inl ⟨nil_mem_kstar L, ?_⟩
          rw [← List.nil_append w, ← h]
          exact mem_of_le mul_kstar_le_kstar (append_mem_mul hz (join_mem_kstar hl'))
        · exact Or.inr ⟨[], x, bs, l.flatten, by simp, hx, nil_mem_kstar L,
            by rw [← hz']; exact hz, join_mem_kstar hl', hw⟩

