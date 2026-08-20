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

lemma lt_iff {a b : Tree} : a < b ↔ lvl a < lvl b ∧ ∀ ξ < lvl a, fn a ξ = fn b ξ := by
  rw [lt_iff_le_and_ne, le_def]
  constructor
  · rintro ⟨⟨hle, hag⟩, hne⟩
    exact ⟨lt_of_le_of_ne hle fun h => hne (ext' h hag), hag⟩
  · rintro ⟨hlt, hag⟩
    exact ⟨⟨hlt.le, hag⟩, fun h => absurd (congrArg lvl h) hlt.ne⟩

/-- The node obtained by restricting a node to a smaller level. -/
