import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Set

namespace Frontier

universe u

/-! ## Finite games in mixed strategies

A finite game is given by a finite type of players `I`, a finite nonempty type of pure
strategies `S i` for each player, and a real payoff function
`u : I → ((i : I) → S i) → ℝ`.
-/

variable {I : Type u} [Fintype I] [DecidableEq I]
  {S : I → Type u} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The set of mixed strategy profiles: for each player, a probability distribution on
that player's pure strategies. -/

def dev (u : I → ((i : I) → S i) → ℝ) (i : I) (a : S i) (σ : (i : I) → S i → ℝ) : ℝ :=
  payoff u i (Function.update σ i (pureMix a))

/-- `σ` is a Nash equilibrium: no player can improve their expected payoff by
unilaterally switching to another mixed strategy. -/
