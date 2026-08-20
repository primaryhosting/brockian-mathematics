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

lemma ext' {a b : Tree} (h1 : lvl a = lvl b) (h2 : ∀ ξ < lvl a, fn a ξ = fn b ξ) : a = b := by
  refine Subtype.ext (Prod.ext h1 (funext fun ξ => ?_))
  rcases lt_or_ge ξ (lvl a) with h | h
  · exact h2 ξ h
  · rw [a.2.2.1 ξ h, b.2.2.1 ξ (h1.ge.trans h)]

instance : PartialOrder Tree where
  le a b := lvl a ≤ lvl b ∧ ∀ ξ < lvl a, fn a ξ = fn b ξ
  le_refl a := ⟨le_rfl, fun _ _ => rfl⟩
  le_trans a b c hab hbc := ⟨hab.1.trans hbc.1, fun ξ hξ =>
    (hab.2 ξ hξ).trans (hbc.2 ξ (lt_of_lt_of_le hξ hab.1))⟩
  le_antisymm a b hab hba := ext' (le_antisymm hab.1 hba.1) hab.2

