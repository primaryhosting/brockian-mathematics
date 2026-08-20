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

def posFrom (p : List X) (σ τ : Strategy X) : ℕ → List X
  | 0 => p
  | n + 1 => posFrom p σ τ n ++ [nextMove σ τ (posFrom p σ τ n)]

variable [Nonempty X]

/-- The infinite play resulting from starting at position `p` and following `σ`, `τ`. -/
