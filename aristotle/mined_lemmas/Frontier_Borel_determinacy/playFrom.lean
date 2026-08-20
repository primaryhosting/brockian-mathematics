import Mathlib
/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

variable {X : Type u}

/-- A strategy assigns a move to every finite position of the game. -/
abbrev Strategy (X : Type u) := List X → X

/-- The move played at position `q`: player I (resp. II) moves at positions of
even (resp. odd) length. -/

noncomputable def playFrom (p : List X) (σ τ : Strategy X) : ℕ → X :=
  fun k => (posFrom p σ τ (k + 1)).getD k (Classical.arbitrary X)

/-- Player I wins the game with payoff `A` from position `p`. -/
