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

theorem continuous_rowValue [Nonempty n] (A : m → n → ℝ) : Continuous (rowValue A) := by
  have : Continuous fun x : m → ℝ =>
      Finset.univ.inf' (Finset.univ_nonempty (α := n)) (fun j => colPayoff A x j) :=
    Continuous.finset_inf'_apply _ fun j _ => continuous_colPayoff A j
  exact this

omit [DecidableEq n] in
/-- The row player has an optimal (maximin) mixed strategy. -/
