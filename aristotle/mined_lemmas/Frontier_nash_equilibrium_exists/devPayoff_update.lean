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

theorem devPayoff_update (G : FiniteGame ι S) (i : ι) (s : S i)
    (x : (i : ι) → S i → ℝ) (y : S i → ℝ) :
    devPayoff G i s (Function.update x i y) = devPayoff G i s x := by
  simp [devPayoff, Function.update_idem]

/-- Expanding the expected payoff along player `i`'s own mixed strategy. -/
