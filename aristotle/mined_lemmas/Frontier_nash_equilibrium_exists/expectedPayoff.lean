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

noncomputable def expectedPayoff (G : FiniteGame ι S) (i : ι) (x : (i : ι) → S i → ℝ) : ℝ :=
  ∑ s : ((i : ι) → S i), (∏ j, x j (s j)) * G.payoff i s

/-- The expected payoff of player `i` when he deviates to the pure strategy `s`. -/
