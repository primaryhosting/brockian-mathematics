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

theorem prod_update_apply (i : ι) (x : (i : ι) → S i → ℝ) (v : S i → ℝ)
    (σ : (i : ι) → S i) :
    ∏ j, (Function.update x i v) j (σ j)
      = v (σ i) * ∏ j ∈ Finset.univ.erase i, x j (σ j) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => Function.update x i v j (σ j))
    (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The deviation payoff does not depend on player `i`'s own mixed strategy. -/
