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

def UnravelsBorel (A : Type u) [TopologicalSpace A] : Prop :=
  ∀ S : Set (ℕ → A), @MeasurableSet (ℕ → A) (borel (ℕ → A)) S →
    ∃ (B : Type u) (cov : Covering A B), Nonempty (Inhabited B) ∧ IsClopenSeq (cov.push ⁻¹' S)

/-- A payoff set that is already clopen is unravelled by the identity covering; in particular the
unravelling condition is satisfiable. -/
