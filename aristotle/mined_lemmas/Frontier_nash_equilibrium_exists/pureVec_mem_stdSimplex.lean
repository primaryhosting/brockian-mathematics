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

theorem pureVec_mem_stdSimplex {α : Type} [Fintype α] [DecidableEq α] (s : α) :
    pureVec s ∈ stdSimplex ℝ α := by
  constructor
  · intro t
    by_cases h : t = s <;> simp [pureVec, h]
  · simp [pureVec]

/-! ### Multilinearity of the expected payoff -/

omit [(i : ι) → Fintype (S i)] [(i : ι) → DecidableEq (S i)] in
/-- Splitting the product defining the expected payoff along player `i`'s coordinate. -/
