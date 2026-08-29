import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file contains auxiliary material used in the construction of an Aronszajn tree:
basic facts about countable ordinals, a dependent-choice helper, and the key
"extension" lemma for almost-disjoint modifications of injections into `ℕ`.
-/

namespace Aronszajn

open Set Cardinal Ordinal
open scoped Ordinal

/-! ### Countability of initial segments -/

/-- An initial segment of the ordinals is countable iff it lies below `ω₁`. -/

theorem image_subset_of_diffSet (α : Ordinal.{0}) (f g : Ordinal.{0} → ℕ) :
    g '' Set.Iio α ⊆ f '' Set.Iio α ∪ g '' (diffSet α f g) := by
  rintro n ⟨γ, hγ, rfl⟩
  by_cases h : f γ = g γ
  · exact Or.inl ⟨γ, hγ, h⟩
  · exact Or.inr ⟨γ, ⟨hγ, h⟩, rfl⟩

