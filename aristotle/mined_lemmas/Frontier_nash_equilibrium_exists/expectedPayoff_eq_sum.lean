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

theorem expectedPayoff_eq_sum (x : ∀ i, S i → ℝ) (i k : I) :
    expectedPayoff S u x k
      = ∑ s : S i, x i s * expectedPayoff S u (Function.update x i (Pi.single s 1)) k := by
  conv_lhs => rw [← Function.update_eq_self i x]
  exact expectedPayoff_update_eq_sum u x i k (x i)

/-! ### Continuity -/

omit [∀ i, DecidableEq (S i)] in
