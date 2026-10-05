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

def BrouwerFixedPoint (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ K : Set E, K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ f : E → E, ContinuousOn f K → Set.MapsTo f K K → ∃ x ∈ K, f x = x

/-! ## Payoff algebra -/

/-- Expected payoff of player `i` when they play the pure strategy `s` and the others
play according to `x` (the `i`-th coordinate of `x` is ignored). -/
