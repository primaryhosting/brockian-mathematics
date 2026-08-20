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

lemma ee_of_good {α ξ : Ordinal.{0}} (h : ∃ n : ℕ, Good α ξ n) :
    ee α ξ = max (ee (cs α (kk α ξ)) ξ) (kk α ξ) := by
  classical
  rw [ee]; exact dif_pos h

