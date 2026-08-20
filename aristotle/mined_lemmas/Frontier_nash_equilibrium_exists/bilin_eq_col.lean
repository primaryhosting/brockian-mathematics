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

theorem bilin_eq_col (A : m → n → ℝ) (x : m → ℝ) (y : n → ℝ) :
    bilin A x y = ∑ j, y j * colPayoff A x j := by
  rw [bilin, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [colPayoff, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [Fintype m] [DecidableEq m] in
