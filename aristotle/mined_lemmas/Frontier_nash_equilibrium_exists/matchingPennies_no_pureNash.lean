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

theorem matchingPennies_no_pureNash :
    ¬ ∃ s : (b : Bool) → twoStrat Bool Bool b,
      IsPureNash (zeroSumGame matchingPennies) s := by
  rintro ⟨s, hs⟩
  by_cases h : (s true : Bool) = (s false : Bool)
  · have hdev := hs false (!(s false))
    simp [zeroSumGame, matchingPennies, h] at hdev
    linarith
  · have hdev := hs true (s false)
    simp [zeroSumGame, matchingPennies, h] at hdev
    linarith

/-- The uniform mixed strategy over a coin flip. -/
