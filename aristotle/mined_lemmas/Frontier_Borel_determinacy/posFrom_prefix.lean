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

theorem posFrom_prefix (p : List X) (σ τ : Strategy X) {n m : ℕ} (h : n ≤ m) :
    posFrom p σ τ n <+: posFrom p σ τ m := by
  induction h with
  | refl => exact List.prefix_rfl
  | step h ih => exact ih.trans (posFrom_prefix_succ _ _ _ _)

