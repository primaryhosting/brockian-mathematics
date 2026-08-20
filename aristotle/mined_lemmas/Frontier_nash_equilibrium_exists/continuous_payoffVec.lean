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

theorem continuous_payoffVec (A : m → n → ℝ) : Continuous (payoffVec A) := by
  refine continuous_pi fun i => continuous_finset_sum _ fun j _ => ?_
  exact (continuous_apply j).mul continuous_const

/-! ### Representation of continuous linear functionals on `m → ℝ` -/

