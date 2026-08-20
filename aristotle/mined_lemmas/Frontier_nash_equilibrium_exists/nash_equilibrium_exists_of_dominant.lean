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

theorem nash_equilibrium_exists_of_dominant (G : FiniteGame ι S) (s : (i : ι) → S i)
    (hdom : ∀ (i : ι) (σ : (i : ι) → S i) (t : S i),
      G.payoff i (Function.update σ i t) ≤ G.payoff i (Function.update σ i (s i))) :
    ∃ x : (i : ι) → S i → ℝ, IsNash G x := by
  refine nash_equilibrium_exists_of_pureNash G (s := s) fun i t => ?_
  have h := hdom i s t
  rwa [Function.update_eq_self] at h

/-- Unconditionally (no Brouwer needed): a finite *potential* game has a Nash
equilibrium; indeed a maximizer of the potential is a pure Nash equilibrium. -/
