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

theorem expectedPayoff_pure (G : FiniteGame ι S) (i : ι) (σ : (i : ι) → S i) :
    expectedPayoff G i (fun j => pureVec (σ j)) = G.payoff i σ := by
  unfold expectedPayoff
  rw [Finset.sum_eq_single σ]
  · simp [pureVec]
  · intro τ _ hτ
    have : ∃ j, τ j ≠ σ j := by
      by_contra h
      push_neg at h
      exact hτ (funext h)
    obtain ⟨j, hj⟩ := this
    have : ∏ k, pureVec (σ k) (τ k) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [pureVec, hj])
    rw [this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A pure Nash equilibrium gives a mixed Nash equilibrium. -/
