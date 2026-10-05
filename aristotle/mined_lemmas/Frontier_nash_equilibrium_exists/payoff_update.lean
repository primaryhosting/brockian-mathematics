/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-! ## Finite games in normal form -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A probability distribution on the (finite) pure strategy set of a player. -/

lemma payoff_update (u : ι → (∀ j, S j) → ℝ) (i : ι) (x : ∀ j, S j → ℝ) (z : S i → ℝ) :
    payoff u i (Function.update x i z)
      = ∑ p : (∀ j, S j), z (p i) * ((∏ j ∈ univ.erase i, x j (p j)) * u i p) := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [prod_update_eq, mul_assoc]

/-- The expected payoff is linear in the deviating player's mixed strategy. -/
