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

noncomputable def cs (α : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  open Classical in
  if h : ∃ g : ℕ → Ordinal.{0}, ∀ ξ < α, ∃ n, ξ ≤ g n ∧ g n < α then h.choose else fun _ => 0

/-- `Good α ξ n` says that stage `cs α n` is below `α` and reaches at least `ξ`. -/
