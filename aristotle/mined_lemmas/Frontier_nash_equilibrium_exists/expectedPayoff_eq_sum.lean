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

theorem expectedPayoff_eq_sum (G : FiniteGame ι S) (i : ι) (x : (i : ι) → S i → ℝ) :
    expectedPayoff G i x = ∑ s : S i, x i s * devPayoff G i s x := by
  simp only [expectedPayoff, devPayoff, Finset.mul_sum, prod_update_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ (fun j => x j (σ j)) (Finset.mem_univ i)]
  simp only [pureVec]
  rw [Finset.sum_eq_single (σ i)]
  · simp; ring
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A mixed profile is a Nash equilibrium iff no player can improve by a *pure* deviation. -/
