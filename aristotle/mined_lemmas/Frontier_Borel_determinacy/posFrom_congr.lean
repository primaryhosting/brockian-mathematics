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

theorem posFrom_congr (p : List X) {σ σ' τ τ' : Strategy X}
    (hσ : ∀ q, p <+: q → σ q = σ' q) (hτ : ∀ q, p <+: q → τ q = τ' q) (n : ℕ) :
    posFrom p σ τ n = posFrom p σ' τ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpre : p <+: posFrom p σ τ n := by
      have := posFrom_prefix p σ τ (Nat.zero_le n)
      simpa [posFrom] using this
    rw [posFrom, posFrom, ih, nextMove, nextMove, ← ih, hσ _ hpre, hτ _ hpre, ih]

