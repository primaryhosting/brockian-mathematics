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

lemma ee_coherent {α β : Ordinal.{0}} (hα : α < ω₁) (hβ : β < α) :
    {ξ : Ordinal.{0} | ξ < β ∧ ee α ξ ≠ ee β ξ}.Finite := (ee_main α hα).2 β hβ

/-! ## The tree -/

/-- Restriction of a function to the ordinals below `γ` (with junk value `0` elsewhere). -/
