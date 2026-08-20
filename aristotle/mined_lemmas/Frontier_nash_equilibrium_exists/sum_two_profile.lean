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

theorem sum_two_profile (f : ((b : Bool) → twoStrat m n b) → ℝ) :
    ∑ σ : ((b : Bool) → twoStrat m n b), f σ = ∑ i : m, ∑ j : n, f (twoProfile i j) := by
  have h1 : ∑ σ : ((b : Bool) → twoStrat m n b), f σ = ∑ p : m × n, f (twoProfile p.1 p.2) :=
    Fintype.sum_equiv (twoProfileEquiv m n) _ _ fun σ => by
      congr 1
      funext b
      cases b <;> rfl
  rw [h1, Fintype.sum_prod_type]

/-- The two player zero sum game with payoff matrix `A`: the row player `true` receives
`A i j` and the column player `false` receives `-A i j`. -/
