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

def IIWins (A : Set (ℕ → X)) (p : List X) : Prop :=
  ∃ τ : Strategy X, ∀ σ : Strategy X, playFrom p σ τ ∉ A

/-- The game with payoff set `A` (played from the empty position) is determined. -/
