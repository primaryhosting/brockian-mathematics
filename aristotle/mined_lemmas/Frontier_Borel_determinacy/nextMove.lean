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

def nextMove (σ τ : Strategy X) (q : List X) : X :=
  if Even q.length then σ q else τ q

/-- The position reached after `n` further moves, starting from position `p`,
when player I follows `σ` and player II follows `τ`. -/
