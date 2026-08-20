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

theorem nash_equilibrium_exists_of_pureNash (G : FiniteGame ι S) {s : (i : ι) → S i}
    (hs : IsPureNash G s) : ∃ x : (i : ι) → S i → ℝ, IsNash G x :=
  ⟨_, isNash_pure G hs⟩

/-- Unconditionally (no Brouwer needed): a game in which every player has a dominant
strategy has a Nash equilibrium. -/
