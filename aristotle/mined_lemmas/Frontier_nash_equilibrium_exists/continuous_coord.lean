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

lemma continuous_coord (i : ι) (s : S i) :
    Continuous (fun x : (∀ j, S j → ℝ) => x i s) :=
  (continuous_apply s).comp (continuous_apply i)

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] in
