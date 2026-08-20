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

theorem not_IWins_defense {A : Set (ℕ → X)} {q : List X} (hq : ¬ IWins A q)
    (hodd : ¬ Even q.length) : ¬ IWins A (q ++ [defenseStrategy A q]) := by
  classical
  have hex : ∃ b : X, ¬ IWins A (q ++ [b]) := by
    by_contra hcon
    push_neg at hcon
    exact hq (IWins_of_children_odd hodd hcon)
  have hdef : defenseStrategy A q = hex.choose := by
    simp only [defenseStrategy, dif_pos hex]
  rw [hdef]
  exact hex.choose_spec

