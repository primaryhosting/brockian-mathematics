/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

theorem pred_linear (y x x' : Node) (h : x < y) (h' : x' < y) : x ≤ x' ∨ x' ≤ x := by
  rcases le_total x.len x'.len with hle | hle
  · exact Or.inl ⟨hle, fun ξ hξ => (h.le.2 ξ hξ).trans (h'.le.2 ξ (lt_of_lt_of_le hξ hle)).symm⟩
  · exact Or.inr ⟨hle, fun ξ hξ => (h'.le.2 ξ hξ).trans (h.le.2 ξ (lt_of_lt_of_le hξ hle)).symm⟩

