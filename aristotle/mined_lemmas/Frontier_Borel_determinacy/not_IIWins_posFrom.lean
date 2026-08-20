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

theorem not_IIWins_posFrom {A : Set (ℕ → X)} (h : ¬ IIWins A []) (τ : Strategy X) (n : ℕ) :
    ¬ IIWins A (posFrom [] (attackStrategy A) τ n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    set q := posFrom [] (attackStrategy A) τ n with hq
    show ¬ IIWins A (q ++ [nextMove (attackStrategy A) τ q])
    by_cases hpar : Even q.length
    · have hm : nextMove (attackStrategy A) τ q = attackStrategy A q := by
        simp [nextMove, hpar]
      rw [hm]
      exact not_IIWins_attack ih hpar
    · have hm : nextMove (attackStrategy A) τ q = τ q := by simp [nextMove, hpar]
      rw [hm]
      exact fun hc => ih (IIWins_of_child_odd hpar hc)

/-- **Gale–Stewart theorem, closed case**: a game whose payoff set has open complement
(i.e. player I's payoff set is closed) is determined. -/
