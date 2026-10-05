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

lemma mixedProfiles_nonempty [∀ i, Nonempty (S i)] :
    (mixedProfiles S).Nonempty := by
  refine ⟨fun i s => if s = Classical.arbitrary (S i) then 1 else 0, fun i => ⟨fun s => ?_, ?_⟩⟩
  · dsimp only
    split <;> norm_num
  · simp

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] in
