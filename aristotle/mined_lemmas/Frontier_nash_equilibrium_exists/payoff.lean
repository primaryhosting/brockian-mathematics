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

noncomputable def payoff (u : ι → (∀ j, S j) → ℝ) (i : ι) (x : ∀ j, S j → ℝ) : ℝ :=
  ∑ p : (∀ j, S j), (∏ j, x j (p j)) * u i p

/-- `x` is a (mixed strategy) Nash equilibrium: it is a mixed profile, and no player can
strictly increase their expected payoff by unilaterally switching to another mixed strategy. -/
