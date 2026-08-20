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

theorem exists_max_rowValue [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    ∃ x ∈ stdSimplex ℝ m, ∀ x' ∈ stdSimplex ℝ m, rowValue A x' ≤ rowValue A x := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_stdSimplex m).exists_isMaxOn (stdSimplex_nonempty m)
    (continuous_rowValue A).continuousOn
  exact ⟨x, hx, fun x' hx' => hmax hx'⟩

/-! ### The minimax theorem -/

/-- **von Neumann's minimax theorem** / existence of a saddle point: every two player
zero sum finite game has a mixed strategy Nash equilibrium.  This is proved
unconditionally, without Brouwer's fixed point theorem. -/
