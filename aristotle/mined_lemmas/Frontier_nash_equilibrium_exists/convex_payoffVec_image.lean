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

theorem convex_payoffVec_image (A : m → n → ℝ) :
    Convex ℝ (payoffVec A '' stdSimplex ℝ n) := by
  rw [← coe_payoffMap]
  exact (convex_stdSimplex ℝ n).linear_image (payoffMap A)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
