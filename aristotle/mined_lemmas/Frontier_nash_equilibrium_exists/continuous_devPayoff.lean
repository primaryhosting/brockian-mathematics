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

theorem continuous_devPayoff (G : FiniteGame ι S) (i : ι) (s : S i) :
    Continuous fun x : (i : ι) → S i → ℝ => devPayoff G i s x :=
  (continuous_expectedPayoff G i).comp (continuous_update i (pureVec s))

/-! ### Nash's map -/

/-- The "regret" of player `i` for the pure strategy `s` at the profile `x`. -/
