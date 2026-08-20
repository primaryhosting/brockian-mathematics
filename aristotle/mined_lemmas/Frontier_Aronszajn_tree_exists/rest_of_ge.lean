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

lemma rest_of_ge {x : Ordinal.{0} → ℕ} {γ ξ : Ordinal.{0}} (h : γ ≤ ξ) : rest x γ ξ = 0 :=
  if_neg (not_lt.2 h)

/-- Nodes of the tree: a level `β < ω₁` together with a function which agrees below `β` with
some `ee α`, `β ≤ α < ω₁`, and vanishes from `β` on. -/
