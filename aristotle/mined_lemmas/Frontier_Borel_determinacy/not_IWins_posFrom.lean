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

theorem not_IWins_posFrom {A : Set (ℕ → X)} (h : ¬ IWins A []) (σ : Strategy X) (n : ℕ) :
    ¬ IWins A (posFrom [] σ (defenseStrategy A) n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    set q := posFrom [] σ (defenseStrategy A) n with hq
    show ¬ IWins A (q ++ [nextMove σ (defenseStrategy A) q])
    by_cases hpar : Even q.length
    · have hm : nextMove σ (defenseStrategy A) q = σ q := by simp [nextMove, hpar]
      rw [hm]
      exact fun hc => ih (IWins_of_child_even hpar hc)
    · have hm : nextMove σ (defenseStrategy A) q = defenseStrategy A q := by
        simp [nextMove, hpar]
      rw [hm]
      exact not_IWins_defense ih hpar

/-- **Gale–Stewart theorem**: every game with an open payoff set is determined.
This is the base case of Martin's transfinite induction for Borel determinacy. -/
