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

lemma continuous_nashMap (u : ι → (∀ j, S j) → ℝ) : Continuous (nashMap u) := by
  refine continuous_pi fun i => continuous_pi fun s => ?_
  refine Continuous.div ((continuous_coord i s).add (continuous_gain u i s))
    (continuous_const.add (continuous_finset_sum _ fun t _ => continuous_gain u i t)) ?_
  intro x
  have := one_le_denom u i x
  linarith

