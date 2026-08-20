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

theorem exists_rowValue_eq [Nonempty n] (A : m → n → ℝ) (x : m → ℝ) :
    ∃ j, rowValue A x = colPayoff A x j := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := n)) (colPayoff A x)
  exact ⟨j, hj⟩

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
