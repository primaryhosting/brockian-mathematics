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

lemma one_le_denom (u : ι → (∀ j, S j) → ℝ) (i : ι) (x : ∀ j, S j → ℝ) :
    (1 : ℝ) ≤ 1 + ∑ t, gain u i t x := by
  have : (0 : ℝ) ≤ ∑ t, gain u i t x :=
    Finset.sum_nonneg fun t _ => gain_nonneg u i t x
  linarith

omit [∀ i, DecidableEq (S i)] in
