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

lemma payoff_update_eq_sum_dev (u : I → ((i : I) → S i) → ℝ) (i : I)
    (σ : (i : I) → S i → ℝ) (τ : S i → ℝ) :
    payoff u i (Function.update σ i τ) = ∑ a : S i, τ a * dev u i a σ := by
  rw [payoff_eq_sum_dev u i (Function.update σ i τ)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Function.update_self, dev_update]

/-- If no pure deviation is profitable then no mixed deviation is either. -/
