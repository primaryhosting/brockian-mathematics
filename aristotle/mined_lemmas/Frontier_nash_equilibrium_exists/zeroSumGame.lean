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

def zeroSumGame (A : m → n → ℝ) : FiniteGame Bool (twoStrat m n) where
  payoff := fun b σ => cond b (A (σ true) (σ false)) (-(A (σ true) (σ false)))

omit [DecidableEq m] [DecidableEq n] in
