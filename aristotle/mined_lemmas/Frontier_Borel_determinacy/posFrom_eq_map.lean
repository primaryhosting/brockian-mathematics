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

theorem posFrom_eq_map (p : List X) (σ τ : Strategy X) (n : ℕ) :
    posFrom p σ τ n = (List.range (p.length + n)).map (playFrom p σ τ) := by
  apply List.ext_getElem
  · simp [posFrom_length]
  · intro k h₁ h₂
    rw [posFrom_length] at h₁
    rw [List.getElem_map, List.getElem_range]
    rw [playFrom_eq_getD p σ τ n k h₁, List.getD_eq_getElem]

omit [Nonempty X] in
