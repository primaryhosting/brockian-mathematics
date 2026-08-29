/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above repeats verbatim as a module docstring below; Lean 4 does not allow a
-- module docstring to precede the `import` commands.)

import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Infinite two-player games on sequences -/

/-- A strategy is a map from the finite history of moves played so far to the next move. -/

def ConsI (p : List A) (σ : Strategy A) (x : ℕ → A) : Prop :=
  hist x p.length = p ∧ ∀ n, p.length ≤ n → Even n → x n = σ (hist x n)

/-- `ConsII p τ x` : the play `x` extends the position `p` and player II (who moves at the odd
positions) follows the strategy `τ` from `p` onwards. -/
