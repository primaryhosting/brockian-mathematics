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

noncomputable def colPayoff (A : m → n → ℝ) (x : m → ℝ) : n → ℝ := fun j => ∑ i, x i * A i j

/-- The expected payoff to the row player of the mixed strategy pair `(x, y)`. -/
