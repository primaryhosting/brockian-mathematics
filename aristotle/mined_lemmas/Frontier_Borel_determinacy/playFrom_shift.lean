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

theorem playFrom_shift (p : List X) (σ τ : Strategy X) :
    playFrom (p ++ [nextMove σ τ p]) σ τ = playFrom p σ τ := by
  funext k
  have h : playFrom (p ++ [nextMove σ τ p]) σ τ k
      = (posFrom (p ++ [nextMove σ τ p]) σ τ (k + 1)).getD k (Classical.arbitrary X) := rfl
  rw [h, posFrom_shift]
  exact (playFrom_eq_getD p σ τ (k + 2) k (by omega)).symm

omit [Nonempty X] in
