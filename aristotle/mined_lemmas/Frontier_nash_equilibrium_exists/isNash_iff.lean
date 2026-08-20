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

theorem isNash_iff (G : FiniteGame ι S) {x : (i : ι) → S i → ℝ} (hx : IsMixed x) :
    IsNash G x ↔ ∀ i, ∀ s : S i, devPayoff G i s x ≤ expectedPayoff G i x := by
  constructor
  · intro hN i s
    exact hN.2 i (pureVec s) (pureVec_mem_stdSimplex s)
  · intro h
    refine ⟨hx, fun i y hy => ?_⟩
    have h1 : expectedPayoff G i (Function.update x i y)
        = ∑ s : S i, y s * devPayoff G i s x := by
      rw [expectedPayoff_eq_sum G i (Function.update x i y)]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Function.update_self, devPayoff_update]
    have h2 : ∑ s : S i, y s * devPayoff G i s x
        ≤ ∑ s : S i, y s * expectedPayoff G i x := by
      refine Finset.sum_le_sum fun s _ => ?_
      exact mul_le_mul_of_nonneg_left (h i s) (hy.1 s)
    have h3 : ∑ s : S i, y s * expectedPayoff G i x = expectedPayoff G i x := by
      rw [← Finset.sum_mul, hy.2, one_mul]
    rw [h1]
    exact h2.trans_eq h3

/-! ### Continuity -/

omit [(i : ι) → DecidableEq (S i)] in
