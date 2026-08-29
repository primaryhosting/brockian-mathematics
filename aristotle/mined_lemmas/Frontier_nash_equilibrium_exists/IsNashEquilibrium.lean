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

def IsNashEquilibrium (u : ι → (∀ j, S j) → ℝ) (x : ∀ j, S j → ℝ) : Prop :=
  IsMixed x ∧ ∀ (i : ι) (z : S i → ℝ), IsDist z →
    payoff u i (Function.update x i z) ≤ payoff u i x

/-- Brouwer's fixed point theorem for the space `E`: every continuous self-map of a
nonempty compact convex subset of `E` has a fixed point. (This is not available in
Mathlib, so it is taken as an explicit hypothesis.) -/
