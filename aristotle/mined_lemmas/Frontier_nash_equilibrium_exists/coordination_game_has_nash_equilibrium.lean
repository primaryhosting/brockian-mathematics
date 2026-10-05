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

theorem coordination_game_has_nash_equilibrium :
    ∃ x : (_ : Fin 2) → Bool → ℝ,
      IsNashEquilibrium (fun _ (p : (_ : Fin 2) → Bool) => if p 0 = p 1 then (1 : ℝ) else 0) x :=
  nash_equilibrium_exists_of_potential _ (fun p => if p 0 = p 1 then (1 : ℝ) else 0)
    (fun _ _ _ => rfl)

/-- A non-triviality check: `IsNashEquilibrium` is not vacuously true. In the one-player
game on `Bool` where action `true` pays `1` and action `false` pays `0`, playing `false`
is not an equilibrium. -/
