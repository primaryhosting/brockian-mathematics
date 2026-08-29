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

theorem determined_of_isClopenSeq {S : Set (ℕ → A)} (hS : IsClopenSeq S) : Determined S :=
  determined_of_isOpenSeq hS.1

/-- **Gale–Stewart theorem**, topological form: a game on a discrete alphabet whose payoff set is
open in the product topology is determined. -/
