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

theorem posFrom_length (p : List X) (σ τ : Strategy X) (n : ℕ) :
    (posFrom p σ τ n).length = p.length + n := by
  induction n with
  | zero => simp [posFrom]
  | succ n ih => simp [posFrom, ih]; omega

omit [Nonempty X] in
