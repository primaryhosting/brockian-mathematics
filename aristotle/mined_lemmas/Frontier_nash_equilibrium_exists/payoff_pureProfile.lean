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

lemma payoff_pureProfile (u : ι → (∀ j, S j) → ℝ) (i : ι) (p : ∀ j, S j) :
    payoff u i (pureProfile p) = u i p := by
  classical
  rw [payoff_eq_sum, Finset.sum_eq_single (p i)]
  · rw [devPayoff_pureProfile, Function.update_eq_self]
    simp [pureProfile]
  · intro s _ hs
    simp [pureProfile, hs]
  · intro h
    exact absurd (mem_univ (p i)) h

/-- **Unconditional existence in potential games.** If the game admits an exact potential
`P`, i.e. every unilateral deviation changes the deviating player's payoff by exactly the
change in `P`, then a maximizer of `P` yields a (pure) Nash equilibrium. No fixed point
