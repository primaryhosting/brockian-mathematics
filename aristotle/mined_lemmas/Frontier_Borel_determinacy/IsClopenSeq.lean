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

def IsClopenSeq (S : Set (ℕ → A)) : Prop := IsOpenSeq S ∧ IsOpenSeq Sᶜ

section Topology

variable [TopologicalSpace A] [DiscreteTopology A]

omit [DiscreteTopology A] in
/-- Openness in the product topology implies the combinatorial notion `IsOpenSeq`. -/
