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

theorem playFrom_at_length (p : List X) (σ τ : Strategy X) :
    playFrom p σ τ p.length = nextMove σ τ p := by
  have h := playFrom_eq_getD p σ τ 1 p.length (by omega)
  simpa [posFrom] using h

