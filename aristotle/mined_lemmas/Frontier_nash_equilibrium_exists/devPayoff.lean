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

noncomputable def devPayoff (G : FiniteGame ι S) (i : ι) (s : S i)
    (x : (i : ι) → S i → ℝ) : ℝ :=
  expectedPayoff G i (Function.update x i (pureVec s))

/-- `x` is a (mixed strategy) Nash equilibrium: it is a mixed profile and no player can
strictly improve his expected payoff by unilaterally switching to another mixed strategy. -/
