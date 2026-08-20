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

theorem playFrom_congr (p : List X) {σ σ' τ τ' : Strategy X}
    (hσ : ∀ q, p <+: q → σ q = σ' q) (hτ : ∀ q, p <+: q → τ q = τ' q) :
    playFrom p σ τ = playFrom p σ' τ' := by
  funext k
  show (posFrom p σ τ (k + 1)).getD k (Classical.arbitrary X)
      = (posFrom p σ' τ' (k + 1)).getD k (Classical.arbitrary X)
  rw [posFrom_congr p hσ hτ]

/-! ### Propagation of winning positions -/

