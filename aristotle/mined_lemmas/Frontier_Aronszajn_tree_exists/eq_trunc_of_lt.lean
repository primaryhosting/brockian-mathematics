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

lemma eq_trunc_of_lt {a b : Tree} (h : b < a) : b = trunc a (lvl b) h.le.1 := by
  refine ext' rfl fun ξ hξ => ?_
  rw [show fn (trunc a (lvl b) h.le.1) ξ = rest (fn a) (lvl b) ξ from rfl, rest_of_lt hξ]
  exact (lt_iff.1 h).2 ξ hξ

/-- The predecessors of a node `a` are order-isomorphic to the ordinals below `lvl a`. -/
