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

theorem playFrom_eq_getD (p : List X) (σ τ : Strategy X) (n k : ℕ)
    (hk : k < p.length + n) :
    playFrom p σ τ k = (posFrom p σ τ n).getD k (Classical.arbitrary X) := by
  have h1 : k < (posFrom p σ τ (k + 1)).length := by
    rw [posFrom_length]; omega
  have h2 : k < (posFrom p σ τ n).length := by rw [posFrom_length]; exact hk
  rcases le_total (k + 1) n with h | h
  · exact getD_of_prefix (posFrom_prefix p σ τ h) h1 _
  · exact (getD_of_prefix (posFrom_prefix p σ τ h) h2 _).symm

