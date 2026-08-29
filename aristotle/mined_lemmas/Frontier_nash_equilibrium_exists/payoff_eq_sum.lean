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

lemma payoff_eq_sum (u : ι → (∀ j, S j) → ℝ) (i : ι) (x : ∀ j, S j → ℝ) :
    payoff u i x = ∑ s, x i s * devPayoff u i s x := by
  conv_lhs => rw [← Function.update_eq_self i x]
  exact payoff_update_eq_sum u i x (x i)

/-- A profile all of whose pure deviations are unprofitable is a Nash equilibrium. -/
