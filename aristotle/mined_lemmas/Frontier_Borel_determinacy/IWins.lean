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

def IWins (A : Set (ℕ → X)) (p : List X) : Prop :=
  ∃ σ : Strategy X, ∀ τ : Strategy X, playFrom p σ τ ∈ A

/-- Player II wins the game with payoff `A` from position `p`. -/
