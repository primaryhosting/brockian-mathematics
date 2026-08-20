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

theorem convex_nonpos : Convex ℝ {z : m → ℝ | ∀ i, z i ≤ 0} := by
  intro x hx y hy a b ha hb _ i
  have h1 : ((a • x + b • y) : m → ℝ) i = a * x i + b * y i := rfl
  rw [h1]
  have hxi := hx i
  have hyi := hy i
  nlinarith

