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

theorem continuous_update (i : ι) (v : S i → ℝ) :
    Continuous fun x : (i : ι) → S i → ℝ => Function.update x i v := by
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h
    simpa [Function.update_self] using (continuous_const : Continuous
      fun _ : (i : ι) → S i → ℝ => v)
  · simpa [Function.update_of_ne h] using (continuous_apply j :
      Continuous fun x : (i : ι) → S i → ℝ => x j)

