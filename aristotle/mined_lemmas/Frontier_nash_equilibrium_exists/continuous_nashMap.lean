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

theorem continuous_nashMap (G : FiniteGame ι S) : Continuous (nashMap G) := by
  refine continuous_pi fun i => continuous_pi fun s => ?_
  have hcoord : Continuous fun x : (i : ι) → S i → ℝ => x i s := by fun_prop
  have hnum : Continuous fun x : (i : ι) → S i → ℝ => x i s + gain G i s x :=
    hcoord.add (continuous_gain G i s)
  have hden : Continuous fun x : (i : ι) → S i → ℝ => 1 + ∑ t : S i, gain G i t x :=
    continuous_const.add (continuous_finset_sum _ fun t _ => continuous_gain G i t)
  exact hnum.div hden fun x => ne_of_gt (one_add_sum_gain_pos G i x)

