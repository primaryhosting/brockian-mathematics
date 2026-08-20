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

theorem continuous_colPayoff (A : m → n → ℝ) (j : n) :
    Continuous fun x : m → ℝ => colPayoff A x j :=
  continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const

omit [DecidableEq m] [DecidableEq n] in
