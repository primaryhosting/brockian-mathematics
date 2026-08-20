/-
Two player zero sum finite games: the von Neumann minimax theorem, proved
unconditionally (via the separating hyperplane theorem, without Brouwer).
This is the unconditional "base case" of Nash's theorem.
-/

import RequestProject.NashEquilibrium

/-!
# Minimax for two player zero sum finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The vector of expected payoffs to the row player against the mixed strategy `y`. -/

def twoProfileEquiv (m n : Type) : ((b : Bool) → twoStrat m n b) ≃ m × n where
  toFun σ := (σ true, σ false)
  invFun p := twoProfile p.1 p.2
  left_inv σ := by
    funext b
    cases b <;> rfl
  right_inv p := rfl

omit [DecidableEq m] [DecidableEq n] in
/-- Summing over pure profiles of a two player game. -/
