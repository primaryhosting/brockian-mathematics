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

theorem nash_equilibrium_exists_zeroSum [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    ∃ z : (b : Bool) → twoStrat m n b → ℝ, IsNash (zeroSumGame A) z := by
  obtain ⟨x, hx, y, hy, hrow, hcol⟩ := exists_saddle_point A
  refine ⟨twoMixed x y, ?_⟩
  have hmix : IsMixed (twoMixed x y) := by
    intro b
    cases b
    · exact hy
    · exact hx
  rw [isNash_iff _ hmix]
  intro b
  cases b
  · -- the column player
    intro t
    rw [devPayoff, expectedPayoff_zeroSum_false, expectedPayoff_zeroSum_false]
    have h1 : (Function.update (twoMixed x y) false (pureVec t)) true = x := rfl
    have h2 : (Function.update (twoMixed x y) false (pureVec t)) false = pureVec t := by
      rw [Function.update_self]
    rw [h1, h2, twoMixed_true, twoMixed_false]
    have := hcol (pureVec t) (pureVec_mem_stdSimplex t)
    linarith
  · -- the row player
    intro s
    rw [devPayoff, expectedPayoff_zeroSum_true, expectedPayoff_zeroSum_true]
    have h1 : (Function.update (twoMixed x y) true (pureVec s)) true = pureVec s := by
      rw [Function.update_self]
    have h2 : (Function.update (twoMixed x y) true (pureVec s)) false = y := rfl
    rw [h1, h2, twoMixed_true, twoMixed_false]
    exact hrow (pureVec s) (pureVec_mem_stdSimplex s)

/-! ### A concrete example: matching pennies -/

/-- Matching pennies: the row player wins the penny iff the two coins agree. -/
