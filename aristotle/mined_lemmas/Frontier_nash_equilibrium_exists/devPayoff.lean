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

noncomputable def devPayoff (u : ι → (∀ j, S j) → ℝ) (i : ι) (s : S i)
    (x : ∀ j, S j → ℝ) : ℝ :=
  ∑ p : (∀ j, S j), (if p i = s then (1 : ℝ) else 0) *
    ((∏ j ∈ univ.erase i, x j (p j)) * u i p)

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
