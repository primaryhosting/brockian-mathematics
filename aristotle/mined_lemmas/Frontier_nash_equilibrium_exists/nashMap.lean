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

noncomputable def nashMap (G : FiniteGame ι S) (x : (i : ι) → S i → ℝ) :
    (i : ι) → S i → ℝ :=
  fun i s => (x i s + gain G i s x) / (1 + ∑ t : S i, gain G i t x)

