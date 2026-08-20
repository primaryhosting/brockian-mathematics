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

theorem bilin_eq_row (A : m → n → ℝ) (x : m → ℝ) (y : n → ℝ) :
    bilin A x y = ∑ i, x i * payoffVec A y i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [payoffVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq m] [DecidableEq n] in
