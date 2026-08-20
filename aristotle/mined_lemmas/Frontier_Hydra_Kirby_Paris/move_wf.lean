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
namespace KirbyParis

/-!
## Hydras

A *hydra* is a finite rooted tree.  We encode it as an inductive type whose only
constructor takes the (ordered) list of subtrees hanging off the root; the order of the
list carries no meaning, and all statements below are invariant under permuting it.
-/

/-- A hydra: a finite rooted tree, given by the list of subtrees attached to its root. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- The dead hydra: a bare root with no heads. -/

theorem move_wf : WellFounded (fun h' h : Hydra => Move h h') :=
  Subrelation.wf transGen_HR_of_move HR_wf.transGen

end KirbyParis

open KirbyParis in
/-- **Kirby–Paris hydra theorem.**  Every play of the Kirby–Paris hydra game terminates,
no matter which head Hercules cuts and no matter how many copies the hydra grows.

The statement is packaged as three equivalent faces of termination:

1. the relation "`h'` is reachable from `h` by one legal move" is well-founded;
2. there is no infinite play, i.e. no infinite sequence of legal moves;
3. for *every* strategy `s` (a function choosing a legal move at each living hydra) and
   every starting hydra `h`, iterating `s` reaches the dead hydra after finitely many
   steps.

Together with `Frontier.KirbyParis.exists_move` (a living hydra always admits a legal
move) this says that Hercules always wins.

This is the Kirby–Paris theorem, which is true but unprovable in Peano arithmetic; the
proof below is of course carried out in ZFC, where the required transfinite induction is
available. -/
