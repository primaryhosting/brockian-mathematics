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

theorem isClosed_nonpos : IsClosed {z : m → ℝ | ∀ i, z i ≤ 0} := by
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const

omit [Fintype m] [DecidableEq m] in
