import Mathlib

/-!
# The cumulative hierarchy and inaccessible cardinals

This file defines the von Neumann cumulative hierarchy `Frontier.cumul o` inside `ZFSet`,
characterizes its members by rank, and proves the two facts about an inaccessible cardinal `κ`
that are needed to see that `V_κ` is a model of ZFC:

* `Frontier.card_lt_of_rank_lt`: a set of rank `< κ.ord` has cardinality `< κ`;
* `Frontier.rank_range_lt`: `V_κ` is closed under images of small families (replacement).
-/

open Ordinal Cardinal

namespace Frontier

/-- The von Neumann cumulative hierarchy `V_o`, as a `ZFSet`. -/

theorem models_ZFC_iff :
    M ⊨ ZFC ↔ (M ⊨ axExt ∧ M ⊨ axPair ∧ M ⊨ axUnion ∧ M ⊨ axPow ∧ M ⊨ axInf ∧
      M ⊨ axFound ∧ M ⊨ axChoice) ∧
      (∀ n (φ : setLang.Formula (Fin n ⊕ Unit)), M ⊨ axSep n φ) ∧
      (∀ n (φ : setLang.Formula (Fin n ⊕ Bool)), M ⊨ axRep n φ) := by
  constructor
  · intro h
    haveI := h
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      [skip; skip; skip; skip; skip; skip; skip; (intro n φ); (intro n φ)] <;>
      refine Theory.realize_sentence_of_mem ZFC ?_ <;> simp only [ZFC, Set.mem_union,
        Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inl (by tauto))
    · exact Or.inl (Or.inr ⟨⟨n, φ⟩, rfl⟩)
    · exact Or.inr ⟨⟨n, φ⟩, rfl⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hsep, hrep⟩
    refine ⟨fun {σ} hσ => ?_⟩
    simp only [ZFC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hσ
    rcases hσ with ((h | ⟨p, rfl⟩) | ⟨p, rfl⟩)
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · exact hsep p.1 p.2
    · exact hrep p.1 p.2

end Realize

end Frontier

