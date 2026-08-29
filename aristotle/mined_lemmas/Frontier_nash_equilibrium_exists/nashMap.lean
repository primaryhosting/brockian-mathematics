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

noncomputable def nashMap (u : ι → (∀ j, S j) → ℝ) (x : ∀ j, S j → ℝ) : ∀ j, S j → ℝ :=
  fun i s => (x i s + gain u i s x) / (1 + ∑ t, gain u i t x)

