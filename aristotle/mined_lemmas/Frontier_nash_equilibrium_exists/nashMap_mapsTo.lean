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

theorem nashMap_mapsTo (G : FiniteGame ι S) {x : (i : ι) → S i → ℝ} (hx : IsMixed x) :
    IsMixed (nashMap G x) := by
  intro i
  have hpos := one_add_sum_gain_pos G i x
  constructor
  · intro s
    apply div_nonneg _ hpos.le
    exact add_nonneg ((hx i).1 s) (gain_nonneg G i s x)
  · have : ∑ s : S i, nashMap G x i s
        = (∑ s : S i, (x i s + gain G i s x)) / (1 + ∑ t : S i, gain G i t x) := by
      rw [Finset.sum_div]
      rfl
    rw [this, Finset.sum_add_distrib, (hx i).2]
    exact div_self (ne_of_gt hpos)

/-- The key step: at any mixed profile some strategy in the support is not better than
the profile itself. -/
