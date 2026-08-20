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

theorem strongDual_repr (f : StrongDual ℝ (m → ℝ)) (z : m → ℝ) :
    f z = ∑ i, z i * f (Pi.single i 1) := by
  have hz : z = ∑ i, z i • (Pi.single i 1 : m → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; simp [smul_eq_mul]

/-! ### The theorem of the alternative -/

/-- `payoffVec A` as a linear map. -/
