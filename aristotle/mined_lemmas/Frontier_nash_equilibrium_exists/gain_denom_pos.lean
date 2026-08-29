/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Set Function

namespace Frontier

/-! ## Finite games in normal form

A finite game in normal form consists of a finite set of players `I`, for each player a finite
nonempty set of pure strategies `S i`, and a payoff function `u i : (∀ j, S j) → ℝ`.

A *mixed strategy* for player `i` is an element of `stdSimplex ℝ (S i)`, and a *mixed strategy
profile* is an element of the product of these simplices. -/

section Game

variable {I : Type} [Fintype I] [DecidableEq I]
  (S : I → Type) [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  (u : I → (∀ i, S i) → ℝ)

/-- The set of mixed strategy profiles of a finite game. -/

theorem gain_denom_pos (x : ∀ i, S i → ℝ) (i : I) :
    (0 : ℝ) < 1 + ∑ t : S i, gain u x i t :=
  lt_of_lt_of_le zero_lt_one (one_le_gain_denom u x i)

/-- Nash's map: each player shifts weight towards the pure strategies that would improve
their payoff, and renormalises. -/
