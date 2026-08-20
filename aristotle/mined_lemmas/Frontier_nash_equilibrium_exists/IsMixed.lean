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

def IsMixed (x : (i : ι) → S i → ℝ) : Prop := ∀ i, x i ∈ stdSimplex ℝ (S i)

/-- The pure strategy `s`, viewed as a mixed strategy (a Dirac vector). -/
