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

theorem sum_gain_nonneg (G : FiniteGame ι S) (i : ι) (x : (i : ι) → S i → ℝ) :
    0 ≤ ∑ t : S i, gain G i t x :=
  Finset.sum_nonneg fun t _ => gain_nonneg G i t x

