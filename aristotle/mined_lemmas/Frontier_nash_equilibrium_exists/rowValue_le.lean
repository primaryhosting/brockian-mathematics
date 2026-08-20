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

theorem rowValue_le [Nonempty n] (A : m → n → ℝ) (x : m → ℝ) (j : n) :
    rowValue A x ≤ colPayoff A x j :=
  Finset.inf'_le _ (Finset.mem_univ j)

omit [DecidableEq m] [DecidableEq n] in
