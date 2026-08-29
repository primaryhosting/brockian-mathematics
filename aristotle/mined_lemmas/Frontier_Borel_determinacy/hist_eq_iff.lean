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

lemma hist_eq_iff (x y : ℕ → A) (n : ℕ) :
    hist x n = hist y n ↔ ∀ i < n, x i = y i := by
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    simpa [hist, List.getElem?_map, hi] using this
  · intro h
    simp only [hist]
    exact List.map_congr_left (by simpa using h)

/-- `ConsI p σ x` : the play `x` extends the position `p` and player I (who moves at the even
positions) follows the strategy `σ` from `p` onwards. -/
