import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A *hydra* is a finite rooted tree: `node l` is the hydra whose root has the
subtrees in the list `l` hanging from it.  (The order of the children is irrelevant
to the game; it is only a bookkeeping device here.)  The *heads* of a hydra are its
leaves, i.e. the occurrences of `node []`. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The list of subtrees hanging from the root. -/

theorem cutTop_moveRel {H H' : Hydra} (h : CutTop H H') : MoveRel H' H := ⟨0, Or.inl h⟩

