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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace PCA.Isolation

/-- Reflexive-transitive closure of a relation, used for heap reachability:
`ReachGen r a b` holds when `b` is reached from `a` by finitely many `r`-steps. -/
inductive ReachGen {V : Type u} (r : V → V → Prop) (a : V) : V → Prop
  /-- Zero steps. -/
  | refl : ReachGen r a a
  /-- One more step at the end of a path. -/
  | tail {b c : V} : ReachGen r a b → r b c → ReachGen r a c

/-- A model of the isolation engine's view of a heap: a points-to relation `edge`
on locations, a predicate `owned` marking the locations owned by the isolated
region, and a distinguished entry point `root` (the reference handed out at the
region boundary). -/
structure IsoModel (V : Type u) where
  /-- `edge a b` means location `a` holds a reference to location `b`. -/
  edge : V → V → Prop
  /-- `owned v` means location `v` belongs to the isolated region. -/
  owned : V → Prop
  /-- The entry point of the traversal. -/
  root : V

variable {V : Type u} (M : IsoModel V)

/-- `Reach M v`: `v` is reachable from the root along points-to edges. -/

theorem owned_of_ownedReach {v : V} (hroot : M.owned M.root) (h : OwnedReach M v) :
    M.owned v := by
  induction h with
  | refl => exact hroot
  | tail _ hstep _ => exact hstep.2.2

/-- Key step: every reachable location either lies in the owned closure, or the
engine has already flagged an escape. -/
