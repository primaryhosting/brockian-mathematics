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

theorem stdSimplex_nonempty (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    (stdSimplex ℝ α).Nonempty :=
  ⟨pureVec (Classical.arbitrary α), pureVec_mem_stdSimplex _⟩

/-- **Theorem of the alternative.** Either the column player can guarantee a nonpositive
payoff to the row player, or the row player has a mixed strategy which is strictly
profitable against every column. -/
