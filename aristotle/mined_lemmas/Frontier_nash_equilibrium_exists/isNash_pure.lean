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

theorem isNash_pure (G : FiniteGame ι S) {s : (i : ι) → S i} (hs : IsPureNash G s) :
    IsNash G (fun i => pureVec (s i)) := by
  have hx : IsMixed (fun i => pureVec (s i)) := fun i => pureVec_mem_stdSimplex _
  rw [isNash_iff G hx]
  intro i t
  have hup : Function.update (fun j => pureVec (s j)) i (pureVec t)
      = fun j => pureVec (Function.update s i t j) := by
    funext j
    by_cases h : j = i
    · subst h
      simp [Function.update_self]
    · simp [Function.update_of_ne h]
  rw [devPayoff, hup, expectedPayoff_pure, expectedPayoff_pure]
  exact hs i t

/-- Unconditionally (no Brouwer needed): a game with a pure Nash equilibrium has a mixed
strategy Nash equilibrium. -/
