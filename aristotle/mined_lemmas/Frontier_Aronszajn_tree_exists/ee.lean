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

noncomputable def ee : Ordinal.{0} → Ordinal.{0} → ℕ
  | α => fun ξ =>
    open Classical in
    if _h : ∃ n : ℕ, Good α ξ n then max (ee (cs α (kk α ξ)) ξ) (kk α ξ) else 0
  termination_by α => α
  decreasing_by exact (kk_spec _h).2

