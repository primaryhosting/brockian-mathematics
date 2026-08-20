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

theorem expectedPayoff_zeroSum_false (A : m → n → ℝ)
    (z : (b : Bool) → twoStrat m n b → ℝ) :
    expectedPayoff (zeroSumGame A) false z = -bilin A (z true) (z false) := by
  rw [expectedPayoff, sum_two_profile, bilin, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.prod_bool]
  simp [zeroSumGame, twoProfile]

/-- **Unconditional Nash existence for two player zero sum finite games.**  No fixed
point theorem is needed: the equilibrium comes from the minimax theorem. -/
