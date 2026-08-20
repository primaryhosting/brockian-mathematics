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

theorem playFrom_of_lt_length (p : List X) (σ τ : Strategy X) {k : ℕ} (hk : k < p.length) :
    playFrom p σ τ k = p.getD k (Classical.arbitrary X) := by
  simpa [posFrom] using playFrom_eq_getD p σ τ 0 k (by omega)

