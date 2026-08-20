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

lemma ee_eq_zero_of_ge {α ξ : Ordinal.{0}} (h : α ≤ ξ) : ee α ξ = 0 := by
  apply ee_of_not_good
  rintro ⟨n, h1, h2⟩
  exact absurd (h.trans h1) (not_le.2 h2)

/-- If all fibers of `ee γ` below `γ` are finite, so are the sets where `ee γ` is `≤ n`. -/
