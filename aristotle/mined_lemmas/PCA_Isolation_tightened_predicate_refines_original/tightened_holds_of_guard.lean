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
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-- A state of the isolated component: the capabilities it currently holds
and the amount of fuel (resource budget) it may still consume. -/
structure State where
  /-- Capabilities held by the component, identified by natural numbers. -/
  caps : List Nat
  /-- Remaining resource budget. -/
  fuel : Nat

/-- A predicate of the isolation engine's model: a property of states. -/
structure Predicate where
  /-- The underlying property of states. -/
  holds : State → Prop

/-- `Refines p q` says that `p` is at least as strong as `q`: every state admitted
by `p` is admitted by `q`. -/

theorem tightened_holds_of_guard (p : Predicate) (s : State) (g : State → Prop)
    (hp : p.holds s) (hg : g s) : ((Tightening.guard g).apply p).holds s :=
  ⟨hp, hg⟩

end PCA.Isolation

