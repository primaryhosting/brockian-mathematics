import Mathlib
-- (Lean 4 requires `import` commands to precede any module docstring, so the required
-- header comment is reproduced verbatim immediately below.)

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Set Cardinal
open scoped Ordinal

namespace Aronszajn

/-! ## Countable ordinals -/

/-- An ordinal is countable (i.e. its set of predecessors is countable) iff it is `< ω₁`. -/

lemma level_countable (β : Ordinal.{0}) : {a : Tree | lvl a = β}.Countable := by
  classical
  by_cases hβ : β < ω₁
  · set D : Tree → Set (Ordinal.{0} × ℕ) := fun a =>
      {p | p.1 < β ∧ fn a p.1 = p.2 ∧ fn a p.1 ≠ ee β p.1} with hDdef
    have hdiff : ∀ a : Tree, lvl a = β →
        {ξ : Ordinal.{0} | ξ < β ∧ fn a ξ ≠ ee β ξ}.Finite := by
      intro a ha
      obtain ⟨_, _, α, hle, hα, hval⟩ := a.2
      have hle' : β ≤ α := ha ▸ hle
      rcases eq_or_lt_of_le hle' with heq | hlt
      · refine Set.Finite.subset Set.finite_empty ?_
        rintro ξ ⟨h1, h2⟩
        exact absurd ((hval ξ (by rw [← ha] at h1; exact h1)).trans (by rw [heq])) h2
      · refine Set.Finite.subset (ee_coherent hα hlt) ?_
        rintro ξ ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [← hval ξ (by rw [← ha] at h1; exact h1)]
        exact h2
    have hfin : ∀ a : Tree, lvl a = β → (D a).Finite := by
      intro a ha
      refine Set.Finite.subset ((hdiff a ha).image (fun ξ => (ξ, fn a ξ))) ?_
      rintro ⟨ξ, v⟩ ⟨h1, h2, h3⟩
      exact ⟨ξ, ⟨h1, h3⟩, by simp [h2]⟩
    have hsub : ∀ a : Tree, D a ⊆ Set.Iio β ×ˢ (Set.univ : Set ℕ) := by
      rintro a ⟨ξ, v⟩ ⟨h1, _, _⟩
      exact ⟨h1, Set.mem_univ _⟩
    have hinj : Set.InjOn D {a : Tree | lvl a = β} := by
      intro a ha b hb hab
      have key : ∀ ξ < β, fn a ξ = fn b ξ := by
        intro ξ hξ
        by_cases h1 : fn a ξ = ee β ξ
        · by_cases h2 : fn b ξ = ee β ξ
          · rw [h1, h2]
          · have hmem : ((ξ, fn b ξ) : Ordinal.{0} × ℕ) ∈ D b := ⟨hξ, rfl, h2⟩
            rw [← hab] at hmem
            simpa using hmem.2.1
        · have hmem : ((ξ, fn a ξ) : Ordinal.{0} × ℕ) ∈ D a := ⟨hξ, rfl, h1⟩
          rw [hab] at hmem
          simpa using hmem.2.1.symm
      exact ext' (ha.trans hb.symm) (fun ξ hξ => key ξ (ha ▸ hξ))
    refine Set.countable_of_injective_of_countable_image hinj ?_
    refine Set.Countable.mono (?_ : D '' {a : Tree | lvl a = β} ⊆
      {t : Set (Ordinal.{0} × ℕ) | t.Finite ∧ t ⊆ Set.Iio β ×ˢ (Set.univ : Set ℕ)}) ?_
    · rintro t ⟨a, ha, rfl⟩
      exact ⟨hfin a ha, hsub a⟩
    · exact Set.countable_setOf_finite_subset
        (Set.Countable.prod ((countable_Iio_iff β).2 hβ) Set.countable_univ)
  · refine Set.Countable.mono (?_ : {a : Tree | lvl a = β} ⊆ ∅) Set.countable_empty
    intro a ha
    exact absurd (ha ▸ lvl_lt_omega1 a) hβ

