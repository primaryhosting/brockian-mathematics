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

theorem nash_equilibrium_exists [∀ i, Nonempty (S i)]
    (hB : BrouwerFixedPoint (∀ i, S i → ℝ)) (u : ι → (∀ j, S j) → ℝ) :
    ∃ x : ∀ j, S j → ℝ, IsNashEquilibrium u x := by
  obtain ⟨x, hxK, hfix⟩ := hB (mixedProfiles S) mixedProfiles_nonempty
    mixedProfiles_isCompact mixedProfiles_convex (nashMap u)
    (continuous_nashMap u).continuousOn (nashMap_mapsTo u)
  exact ⟨x, isNashEquilibrium_of_fixed u hxK hfix⟩

/-! ## Unconditional existence for potential games

The reduction above needs Brouwer's fixed point theorem. For the special case of
*potential games* (which includes games of common interest) a pure strategy equilibrium
exists unconditionally: any maximizer of the potential is one. -/

/-- The mixed profile in which every player `j` plays the pure strategy `p j`. -/
