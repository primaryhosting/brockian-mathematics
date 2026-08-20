/-
/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- A *hydra* is a finite rooted tree: a node together with the (finite) list of the
hydras hanging from it.  Only the multiset of children matters for the game, but a list
representation is used so that the type is a genuine inductive type. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- Structural induction principle for hydras: to prove a property of every hydra it
suffices to prove it for `node L` assuming it for every element of `L`. -/

theorem wellFounded_below : WellFounded Below := ⟨acc_below⟩

end Hydra

/-- **The Kirby–Paris hydra theorem.**

Whatever strategy is used — at every stage the player may chop off *any* head, and the
hydra may grow back *any* finite number of copies of the relevant subtree — the game
terminates: the hydra is dead (`Hydra.node []`) after finitely many moves.

Here `H : ℕ → Hydra` is an arbitrary play: as long as the current hydra `H k` is alive,
`H (k+1)` is obtained from it by a legal move (`Hydra.Step`).  The conclusion is that
some `H k` is the dead hydra. -/
