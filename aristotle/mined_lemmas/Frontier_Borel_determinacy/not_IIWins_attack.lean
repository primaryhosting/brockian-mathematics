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

theorem not_IIWins_attack {A : Set (ℕ → X)} {q : List X} (hq : ¬ IIWins A q)
    (heven : Even q.length) : ¬ IIWins A (q ++ [attackStrategy A q]) := by
  classical
  have hex : ∃ a : X, ¬ IIWins A (q ++ [a]) := by
    by_contra hcon
    push_neg at hcon
    exact hq (IIWins_of_children_even heven hcon)
  have hdef : attackStrategy A q = hex.choose := by
    simp only [attackStrategy, dif_pos hex]
  rw [hdef]
  exact hex.choose_spec

