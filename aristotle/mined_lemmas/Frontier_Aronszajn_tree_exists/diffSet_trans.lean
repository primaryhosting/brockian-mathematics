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

theorem diffSet_trans (α : Ordinal.{0}) (f g h : Ordinal.{0} → ℕ) :
    diffSet α f h ⊆ diffSet α f g ∪ diffSet α g h := by
  rintro γ ⟨hγ, hne⟩
  by_cases hfg : f γ = g γ
  · exact Or.inr ⟨hγ, by rw [← hfg]; exact hne⟩
  · exact Or.inl ⟨hγ, hfg⟩

