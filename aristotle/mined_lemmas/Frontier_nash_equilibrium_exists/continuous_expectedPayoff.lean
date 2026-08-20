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

theorem continuous_expectedPayoff (G : FiniteGame ι S) (i : ι) :
    Continuous fun x : (i : ι) → S i → ℝ => expectedPayoff G i x := by
  unfold expectedPayoff
  refine continuous_finset_sum _ fun σ _ => Continuous.mul ?_ continuous_const
  exact continuous_finset_prod _ fun j _ => (continuous_apply (σ j)).comp (continuous_apply j)

omit [Fintype ι] [(i : ι) → Fintype (S i)] [(i : ι) → DecidableEq (S i)] in
